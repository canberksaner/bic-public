/* BIC on a Raspberry Pi Pico 2 W, driven over WiFi (TCP port 4242).
 *
 * The requests and replies are those of bic_service.h. The Pico joins the
 * network named in wifi_credentials.h and prints "BIC WiFi ready at
 * <ip>:4242" over USB serial every two seconds, so a serial monitor shows its
 * address; scripts/pico_run.py finds it by scanning the local network. One
 * client at a time; the link is re-joined if the network drops.
 *
 * The LED shows the state: three quick flashes at power-up, fast blink while
 * joining WiFi, a heartbeat (two short pulses every 1.5 s) when idle, steady
 * on while solving or receiving an update. The LED is switched outside the
 * timed solve.
 *
 * Firmware updates over WiFi (scripts/pico_flash.py, see ota.h):
 *   "OTAQ", uint32 size, uint32 crc32, then the image (.bin)
 *     -> "OTAR", int32 status; on success the Pico reboots into the image
 *   "VERQ" -> "VERR", uint16 minor, uint16 major, int32 partition (0 A, 1 B)
 *
 * lwIP runs in poll mode: everything, including the solve, happens in the
 * main loop, so no locking is needed.
 */
#include <stdio.h>
#include <string.h>

#include "lwip/ip4_addr.h"
#include "lwip/netif.h"
#include "lwip/tcp.h"
#include "lwip/priv/tcp_priv.h"   /* tcp_ack_now */
#include "pico/cyw43_arch.h"
#include "pico/stdlib.h"

#include "bic_service.h"
#include "ota.h"
#include "wifi_credentials.h"

#ifndef BIC_FW_MAJOR
#define BIC_FW_MAJOR 0
#endif
#ifndef BIC_FW_MINOR
#define BIC_FW_MINOR 0
#endif

#define BIC_TCP_PORT 4242
#define OTA_ARGS 8

static struct tcp_pcb *g_client = NULL;

static uint32_t now_ms(void) { return to_ms_since_boot(get_absolute_time()); }

/* ------------------------------------------------------------------ LED */

static int led_now = -1;            /* unknown until the first write */
static uint32_t busy_until_ms = 0;  /* steady on until then */

/* The LED hangs off the wireless chip, so each change is a bus transfer:
 * only write when the state actually changes. */
static void led_set(bool on)
{
    if (led_now != (int)on) {
        cyw43_arch_gpio_put(CYW43_WL_GPIO_LED_PIN, on);
        led_now = on;
    }
}

static bool heartbeat(uint32_t ms)
{
    uint32_t p = ms % 1500;
    return p < 80 || (p >= 220 && p < 300);
}

static void led_update(void)
{
    if ((int32_t)(busy_until_ms - now_ms()) > 0)
        led_set(true);
    else
        led_set(heartbeat(now_ms()));
}

/* Wait while keeping the network alive. */
static void wait_ms_polling(uint32_t ms)
{
    absolute_time_t end = make_timeout_time_ms(ms);
    while (!time_reached(end))
        cyw43_arch_poll();
}

/* ------------------------------------------------------- request parser */

enum { ST_MAGIC, ST_HEADER, ST_PAYLOAD, ST_READY, ST_OTA_ARGS, ST_OTA_DATA,
       ST_OTA_DONE, ST_VER_READY };

static int st = ST_MAGIC;
static uint8_t window[4];           /* last four bytes, for the magic */
static int req_kind = SVC_NONE;
static uint8_t hdr[SVC_REQ_HEADER];
static size_t hdr_got = 0;
static uint32_t req_n = 0;
static uint64_t pay_need = 0, pay_got = 0;
static uint8_t ota_args[OTA_ARGS];
static size_t ota_args_got = 0;
static uint32_t ota_left = 0;
static int32_t ota_status = OTA_OK;

static void parser_reset(void)
{
    st = ST_MAGIC;
    memset(window, 0, sizeof window);
}

static bool request_pending(void)
{
    return st == ST_READY || st == ST_OTA_DONE || st == ST_VER_READY;
}

static void feed(const uint8_t *p, size_t len)
{
    size_t i = 0;
    while (i < len && !request_pending()) {
        if (st == ST_MAGIC) {
            memmove(window, window + 1, 3);
            window[3] = p[i++];
            req_kind = svc_kind(window);
            if (req_kind != SVC_NONE) {
                memcpy(hdr, window, 4);
                hdr_got = 4;
                st = ST_HEADER;
            } else if (memcmp(window, "OTAQ", 4) == 0) {
                ota_args_got = 0;
                st = ST_OTA_ARGS;
            } else if (memcmp(window, "VERQ", 4) == 0) {
                st = ST_VER_READY;
            }
        } else if (st == ST_HEADER) {
            size_t k = SVC_REQ_HEADER - hdr_got;
            if (k > len - i)
                k = len - i;
            memcpy(hdr + hdr_got, p + i, k);
            hdr_got += k;
            i += k;
            if (hdr_got == SVC_REQ_HEADER) {
                memcpy(&req_n, hdr + 4, 4);
                pay_need = (uint64_t)svc_bytes_per_ev(req_kind) * req_n;
                pay_got = 0;
                st = pay_need ? ST_PAYLOAD : ST_READY;
            }
        } else if (st == ST_OTA_ARGS) {
            size_t k = OTA_ARGS - ota_args_got;
            if (k > len - i)
                k = len - i;
            memcpy(ota_args + ota_args_got, p + i, k);
            ota_args_got += k;
            i += k;
            if (ota_args_got == OTA_ARGS) {
                uint32_t size, crc;
                memcpy(&size, ota_args, 4);
                memcpy(&crc, ota_args + 4, 4);
                ota_status = ota_begin(size, crc);
                ota_left = size;
                st = size ? ST_OTA_DATA : ST_OTA_DONE;
            }
        } else if (st == ST_OTA_DATA) {
            /* Written to flash sector by sector as it arrives; after an
             * error the rest is still consumed to stay in step. */
            size_t k = len - i;
            if (k > ota_left)
                k = ota_left;
            ota_feed(p + i, k);
            ota_left -= (uint32_t)k;
            i += k;
            busy_until_ms = now_ms() + 300;
            if (ota_left == 0)
                st = ST_OTA_DONE;
        } else {
            size_t room;
            uint8_t *dst = svc_payload_dest(req_kind, req_n, pay_got, &room);
            size_t k = len - i;
            if ((uint64_t)k > pay_need - pay_got)
                k = (size_t)(pay_need - pay_got);
            if (k > room)
                k = room;
            if (dst)
                memcpy(dst, p + i, k);
            pay_got += k;
            i += k;
            if (pay_got == pay_need)
                st = ST_READY;
        }
    }
}

/* ------------------------------------------------------------ TCP glue */

static void drop_client(void)
{
    if (!g_client)
        return;
    tcp_arg(g_client, NULL);
    tcp_recv(g_client, NULL);
    tcp_err(g_client, NULL);
    if (tcp_close(g_client) != ERR_OK)
        tcp_abort(g_client);
    g_client = NULL;
    parser_reset();
}

static err_t on_recv(void *arg, struct tcp_pcb *pcb, struct pbuf *p, err_t err)
{
    (void)arg;
    (void)err;
    if (p == NULL) {          /* client closed the connection */
        drop_client();
        return ERR_OK;
    }
    for (struct pbuf *q = p; q != NULL; q = q->next)
        feed((const uint8_t *)q->payload, q->len);
    tcp_recved(pcb, p->tot_len);
    pbuf_free(p);
    return ERR_OK;
}

static void on_err(void *arg, err_t err)
{
    (void)arg;
    (void)err;
    g_client = NULL;          /* lwIP has already freed the pcb */
    parser_reset();
}

static err_t on_accept(void *arg, struct tcp_pcb *pcb, err_t err)
{
    (void)arg;
    if (err != ERR_OK || pcb == NULL)
        return ERR_VAL;
    drop_client();            /* one client at a time */
    g_client = pcb;
    tcp_nagle_disable(pcb);   /* send small replies immediately */
    tcp_recv(pcb, on_recv);
    tcp_err(pcb, on_err);
    parser_reset();
    return ERR_OK;
}

/* Queue len bytes, waiting for send-buffer space as needed. */
static bool send_all(const void *buf, size_t len)
{
    /* Bound to the client that asked: if another one connects meanwhile,
     * the rest of this reply is dropped rather than sent to the newcomer. */
    struct tcp_pcb *pcb = g_client;
    const uint8_t *p = buf;
    while (len > 0) {
        if (!g_client || g_client != pcb)
            return false;
        size_t room = tcp_sndbuf(g_client);
        if (room == 0) {
            tcp_output(g_client);
            cyw43_arch_poll();
            continue;
        }
        size_t k = len < room ? len : room;
        if (k > 0xFFFF)
            k = 0xFFFF;
        err_t e = tcp_write(g_client, p, (u16_t)k, TCP_WRITE_FLAG_COPY);
        if (e == ERR_MEM) {
            tcp_output(g_client);
            cyw43_arch_poll();
            continue;
        }
        if (e != ERR_OK)
            return false;
        p += k;
        len -= k;
    }
    tcp_output(g_client);
    return true;
}

static void put_u32(uint8_t *p, uint32_t v) { memcpy(p, &v, 4); }

/* Solve the received request and send the reply. */
static void serve_request(void)
{
    /* Acknowledge the whole request before solving. lwIP does not run during
     * the solve, and a delayed ACK would leave the PC retransmitting for the
     * full solve time (tens of seconds for large instances with a gap) until
     * it gives up on the connection. */
    if (g_client) {
        tcp_ack_now(g_client);
        tcp_output(g_client);
        wait_ms_polling(2);
    }

    uint8_t rep[SVC_REP_HEADER];
    const double *x;
    uint32_t n_out = svc_execute(req_kind, hdr, rep, &x);
    if (send_all(rep, SVC_REP_HEADER))
        send_all(x, 8u * n_out);
}

/* Finish a firmware update: report, and reboot into it if it is good. */
static void serve_ota(void)
{
    int32_t status = ota_status == OTA_OK ? ota_finish() : ota_status;
    uint8_t rep[8];
    memcpy(rep, "OTAR", 4);
    put_u32(rep + 4, (uint32_t)status);
    send_all(rep, sizeof rep);
    if (status == OTA_OK) {
        printf("BIC WiFi: update written, rebooting into it\n");
        wait_ms_polling(300);          /* let the reply leave */
        drop_client();
        wait_ms_polling(200);
        ota_reboot();
    }
}

/* Report the firmware version and the partition it runs from. */
static void serve_version(void)
{
    uint8_t rep[12];
    memcpy(rep, "VERR", 4);
    uint16_t minor = BIC_FW_MINOR, major = BIC_FW_MAJOR;
    memcpy(rep + 4, &minor, 2);
    memcpy(rep + 6, &major, 2);
    put_u32(rep + 8, (uint32_t)ota_running_partition());
    send_all(rep, sizeof rep);
}

/* ---------------------------------------------------------------- WiFi */

/* Join the network, blinking fast meanwhile; retries until it succeeds.
 * Mirrors cyw43_arch_wifi_connect_until, with the LED driven in the loop. */
static void join_wifi(void)
{
    for (;;) {
        if (cyw43_arch_wifi_connect_async(WIFI_SSID, WIFI_PASSWORD,
                                          CYW43_AUTH_WPA2_AES_PSK) == 0) {
            absolute_time_t deadline = make_timeout_time_ms(30000);
            int status = CYW43_LINK_JOIN;
            while (status >= 0 && status != CYW43_LINK_UP && !time_reached(deadline)) {
                cyw43_arch_poll();
                led_set((now_ms() / 125) % 2 == 0);
                status = cyw43_tcpip_link_status(&cyw43_state, CYW43_ITF_STA);
                if (status == CYW43_LINK_NONET) {   /* network not seen yet */
                    status = CYW43_LINK_JOIN;
                    cyw43_arch_wifi_connect_async(WIFI_SSID, WIFI_PASSWORD,
                                                  CYW43_AUTH_WPA2_AES_PSK);
                }
            }
            if (status == CYW43_LINK_UP)
                break;
            printf("BIC WiFi: could not join '%s' (status %d), retrying\n",
                   WIFI_SSID, status);
        }
        wait_ms_polling(1000);
    }

    /* Power saving delays packets by tens of milliseconds; a charging
     * controller on mains power has no reason to use it. */
    cyw43_wifi_pm(&cyw43_state, cyw43_pm_value(CYW43_NO_POWERSAVE_MODE, 20, 1, 1, 1));
}

/* ----------------------------------------------------------------- main */

int main(void)
{
    stdio_init_all();

    if (cyw43_arch_init()) {
        for (;;) {
            printf("BIC WiFi: radio init failed\n");
            sleep_ms(2000);
        }
    }
    cyw43_arch_enable_sta_mode();

    /* Hello: three quick flashes at power-up. */
    for (int k = 0; k < 3; k++) {
        led_set(true);
        sleep_ms(60);
        led_set(false);
        sleep_ms(90);
    }

    join_wifi();

    /* Joining WiFi shows this image works: confirm it, so a flash-update
     * boot keeps it instead of returning to the previous image. */
    int confirmed = ota_confirm();
    printf("BIC WiFi: firmware %d.%d in slot %c, confirm %d\n", BIC_FW_MAJOR,
           BIC_FW_MINOR, "AB"[ota_running_partition() == 1], confirmed);

    struct tcp_pcb *listener = tcp_new_ip_type(IPADDR_TYPE_ANY);
    tcp_bind(listener, NULL, BIC_TCP_PORT);
    listener = tcp_listen_with_backlog(listener, 1);
    tcp_accept(listener, on_accept);

    absolute_time_t next_print = get_absolute_time();
    absolute_time_t next_link_check = make_timeout_time_ms(1000);

    for (;;) {
        cyw43_arch_poll();

        if (st == ST_READY) {
            led_set(true);
            serve_request();
            parser_reset();
            busy_until_ms = now_ms() + 300;
        } else if (st == ST_OTA_DONE) {
            serve_ota();
            parser_reset();
        } else if (st == ST_VER_READY) {
            serve_version();
            parser_reset();
        }
        led_update();

        if (time_reached(next_link_check)) {
            if (cyw43_tcpip_link_status(&cyw43_state, CYW43_ITF_STA) != CYW43_LINK_UP) {
                printf("BIC WiFi: link lost, re-joining\n");
                drop_client();
                join_wifi();
            }
            next_link_check = make_timeout_time_ms(1000);
        }
        if (time_reached(next_print)) {
            printf("BIC WiFi ready at %s:%d (firmware %d.%d, slot %c)\n",
                   ip4addr_ntoa(netif_ip4_addr(&cyw43_state.netif[CYW43_ITF_STA])),
                   BIC_TCP_PORT, BIC_FW_MAJOR, BIC_FW_MINOR,
                   "AB"[ota_running_partition() == 1]);
            next_print = make_timeout_time_ms(2000);
        }
    }
}
