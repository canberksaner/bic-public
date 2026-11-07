/* Request handling of the WiFi firmware (main_wifi.c), also run on the PC by
 * host/bench_host.c. The transport only moves bytes: it
 * finds a request magic, reads the 48-byte header, places the payload where
 * svc_payload_dest says, calls svc_execute, and sends back the reply header
 * and the allocation.
 *
 * Request header (little-endian):
 *   0   char[4]  magic: "BICQ" / "BICM" (utility parameters) or
 *                "EVSQ" / "EVSM" (EV states); the *M kinds carry a maximum
 *                rate per EV, the *Q kinds use the header xmax for every EV
 *   4   uint32   n        number of connected EVs (0 = ping)
 *   8   uint32   reps     solves of the same request (timing)
 *   12  uint32   flags    bit 1 fastpath (bit 0 unused)
 *   16  double   budget   [kW]
 *   24  double   eps
 *   32  double   xmin     [kW]
 *   40  double   xmax     [kW] (rating of every EV for BICQ/EVSQ)
 * Payload:
 *   BICQ: double A[n], B[n], C[n]            (f_i(x) = A_i log(B_i x + C_i))
 *   BICM: double A[n], B[n], C[n], xmax[n]
 *   EVSQ: double t_rem[n], e_rem[n]          remaining parking time [min] and
 *         remaining energy [kWh]; the Pico forms the sLLF utilities itself:
 *         A_i = xmax_i, B_i = 1/xmax_i,
 *         C_i = max(t_rem - 60 e_rem/xmax_i - 1, 1e-6)
 *   EVSM: double t_rem[n], e_rem[n], xmax[n]
 *
 * Reply header:
 *   0   char[4]  "BICR"
 *   4   int32    status   0 ok, -1 n too large, -2/-3 see bic_core.h
 *   8   uint32   n        length of the allocation that follows
 *   12  uint32   path     0 all-max, 1 fast path, 2 choosing phase
 *   16  uint32   c_best   EVs switched on
 *   20  uint32   chain_ok (bits 0-15) and number of rating groups
 *                (bits 16-31, choosing path only)
 *   24  uint32   sys_hz   CPU clock
 *   28  uint32   reps
 *   32  uint64   t_min_us    fastest of the reps, on-chip
 *   40  uint64   t_total_us  sum over the reps
 *   48  double   objval
 * followed by double x[n] [kW]. For EVSQ the on-chip time covers forming the
 * utilities and solving, i.e. the whole controller step.
 */
#ifndef BIC_SERVICE_H
#define BIC_SERVICE_H

#include <stddef.h>
#include <stdint.h>

#include "bic_core.h"

#define SVC_REQ_HEADER 48
#define SVC_REP_HEADER 56

enum { SVC_NONE = 0, SVC_SOLVE = 1, SVC_EV_STATE = 2, SVC_SOLVE_MIXED = 3,
       SVC_EV_STATE_MIXED = 4 };

/* Request kind for a 4-byte magic, SVC_NONE if it is not one. */
BIC_API int svc_kind(const uint8_t magic[4]);

/* Payload bytes per EV for a request kind. */
BIC_API uint32_t svc_bytes_per_ev(int kind);

/* Where payload byte `offset` of an n-EV request goes. *room receives the
 * number of bytes that may be written contiguously from there. Returns NULL
 * when n exceeds the capacity: the transport then discards the payload. */
BIC_API uint8_t *svc_payload_dest(int kind, uint32_t n, uint64_t offset, size_t *room);

/* Run a fully received request. Fills the reply header, points *x at the
 * allocation and returns its length. */
BIC_API uint32_t svc_execute(int kind, const uint8_t hdr[SVC_REQ_HEADER],
                             uint8_t rep[SVC_REP_HEADER], const double **x);

#endif
