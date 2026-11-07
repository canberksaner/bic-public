/* Over-the-air firmware updates for the WiFi firmware, using the RP2350
 * boot ROM's A/B partitions (ota_pt.json).
 *
 * The running image lives in partition A or B. A new image (the .bin of
 * pico_bic_wifi) is streamed into the other partition, checked with CRC-32
 * against what the PC sent and read back from flash, and the Pico reboots
 * into it with a "flash update" boot. Images are built "try before you
 * buy": the new image must call ota_confirm() (after joining WiFi), or the
 * boot ROM's watchdog returns to the previous image. The boot ROM also
 * checks each image's SHA-256 hash before running it.
 */
#ifndef BIC_OTA_H
#define BIC_OTA_H

#include <stddef.h>
#include <stdint.h>

/* Status codes in the OTAR reply. */
#define OTA_OK                0
#define OTA_ERR_NO_PARTITION -10   /* not running from an A/B partition */
#define OTA_ERR_TOO_LARGE    -11   /* image larger than the partition */
#define OTA_ERR_FLASH        -12   /* erase or program failed */
#define OTA_ERR_LENGTH       -13   /* received length differs from announced */
#define OTA_ERR_CRC          -14   /* CRC of received data differs */
#define OTA_ERR_VERIFY       -15   /* flash read-back differs */

/* Start an update of `size` bytes whose CRC-32 is `crc`. */
int32_t ota_begin(uint32_t size, uint32_t crc);

/* Next bytes of the image. Writes each 4 KiB sector as it completes. */
void ota_feed(const uint8_t *p, size_t len);

/* Write the last sector and check the image. OTA_OK when it can be booted. */
int32_t ota_finish(void);

/* Reboot into the updated partition (does not return). */
void ota_reboot(void);

/* Confirm ("buy") the running image after a flash-update boot. Returns the
 * boot ROM result, or 1 if there was nothing to confirm. */
int ota_confirm(void);

/* Partition the running image was booted from (0 = A, 1 = B, -1 none). */
int ota_running_partition(void);

#endif
