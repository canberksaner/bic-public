/* See ota.h. Partition lookup follows pico_cyw43_driver/cyw43_driver.c of
 * the Pico SDK. */
#include <string.h>

#include "boot/picobin.h"
#include "boot/picoboot_constants.h"
#include "hardware/flash.h"
#include "pico/bootrom.h"
#include "pico/flash.h"
#include "pico/stdlib.h"

#include "ota.h"

/* One flash sector of incoming data; doubles as boot ROM work area. */
static uint8_t sector[FLASH_SECTOR_SIZE] __attribute__((aligned(4)));

static uint32_t part_start, part_size;    /* target partition, flash offsets */
static uint32_t expect_size, expect_crc;
static uint32_t received, crc_rx;
static uint32_t sectors_written;
static size_t fill;
static int32_t error;

/* Standard CRC-32 (as zlib.crc32), continued from a previous value. */
static uint32_t crc32_update(uint32_t crc, const uint8_t *p, size_t n)
{
    crc = ~crc;
    while (n--) {
        crc ^= *p++;
        for (int k = 0; k < 8; k++)
            crc = (crc >> 1) ^ (0xEDB88320u & (0u - (crc & 1u)));
    }
    return ~crc;
}

int ota_running_partition(void)
{
    boot_info_t info;
    if (!rom_get_boot_info(&info))
        return -1;
    return info.partition;
}

static bool partition_range(int p, uint32_t *start, uint32_t *size)
{
    uint32_t buf[3];
    rom_load_partition_table(sector, sizeof sector, false);
    int rc = rom_get_partition_table_info(
        buf, 3, PT_INFO_PARTITION_LOCATION_AND_FLAGS | PT_INFO_SINGLE_PARTITION | ((uint32_t)p << 24));
    if (rc != 3 || buf[0] != (PT_INFO_PARTITION_LOCATION_AND_FLAGS | PT_INFO_SINGLE_PARTITION))
        return false;
    uint32_t first = (buf[1] >> PICOBIN_PARTITION_LOCATION_FIRST_SECTOR_LSB) & 0x1fffu;
    uint32_t last = (buf[1] >> PICOBIN_PARTITION_LOCATION_LAST_SECTOR_LSB) & 0x1fffu;
    *start = first * FLASH_SECTOR_SIZE;
    *size = (last + 1 - first) * FLASH_SECTOR_SIZE;
    return true;
}

int32_t ota_begin(uint32_t size, uint32_t crc)
{
    received = crc_rx = sectors_written = 0;
    fill = 0;
    expect_size = size;
    expect_crc = crc;
    error = OTA_OK;

    int running = ota_running_partition();
    if ((running != 0 && running != 1)
        || !partition_range(running == 0 ? 1 : 0, &part_start, &part_size))
        error = OTA_ERR_NO_PARTITION;
    else if (size > part_size)
        error = OTA_ERR_TOO_LARGE;
    return error;
}

typedef struct {
    uint32_t offset;
} write_args_t;

/* Runs with interrupts off and flash not in use (flash_safe_execute). */
static void write_sector_unsafe(void *p)
{
    const write_args_t *w = p;
    flash_range_erase(w->offset, FLASH_SECTOR_SIZE);
    flash_range_program(w->offset, sector, FLASH_SECTOR_SIZE);
}

static void write_sector(void)
{
    if (fill < FLASH_SECTOR_SIZE)
        memset(sector + fill, 0xFF, FLASH_SECTOR_SIZE - fill);
    write_args_t w = {part_start + sectors_written * FLASH_SECTOR_SIZE};
    if (flash_safe_execute(write_sector_unsafe, &w, UINT32_MAX) != PICO_OK)
        error = OTA_ERR_FLASH;
    sectors_written++;
    fill = 0;
}

void ota_feed(const uint8_t *p, size_t len)
{
    if (error != OTA_OK)
        return;
    crc_rx = crc32_update(crc_rx, p, len);
    received += (uint32_t)len;
    while (len > 0 && error == OTA_OK) {
        size_t k = FLASH_SECTOR_SIZE - fill;
        if (k > len)
            k = len;
        memcpy(sector + fill, p, k);
        fill += k;
        p += k;
        len -= k;
        if (fill == FLASH_SECTOR_SIZE)
            write_sector();
    }
}

int32_t ota_finish(void)
{
    if (error != OTA_OK)
        return error;
    if (fill > 0)
        write_sector();
    if (error != OTA_OK)
        return error;
    if (received != expect_size)
        return error = OTA_ERR_LENGTH;
    if (crc_rx != expect_crc)
        return error = OTA_ERR_CRC;

    /* Read the partition back through the untranslated flash window. */
    const uint8_t *flash = (const uint8_t *)(XIP_NOCACHE_NOALLOC_NOTRANSLATE_BASE + part_start);
    if (crc32_update(0, flash, expect_size) != expect_crc)
        return error = OTA_ERR_VERIFY;
    return OTA_OK;
}

void ota_reboot(void)
{
    /* A flash-update boot prefers the partition starting at this address,
     * which also gives the try-before-you-buy image its one trial run. */
    rom_reboot(REBOOT2_FLAG_REBOOT_TYPE_FLASH_UPDATE | REBOOT2_FLAG_NO_RETURN_ON_SUCCESS,
               500, XIP_BASE + part_start, 0);
    for (;;)
        tight_loop_contents();
}

int ota_confirm(void)
{
    boot_info_t info;
    if (!rom_get_boot_info(&info) || (info.boot_type & ~BOOT_TYPE_CHAINED_FLAG) != BOOT_TYPE_FLASH_UPDATE)
        return 1;
    return rom_explicit_buy(sector, sizeof sector);
}
