/* PC timing of the firmware code path, used by scripts/pico_run_pc.py.
 * A complete request message (as built by pico_run.py) is
 * placed exactly as the firmware transports place it, then svc_execute (for
 * EVSQ: forming the utilities and running BIC) is timed `reps` times with
 * the Windows high-resolution counter. Returns the fastest time in seconds,
 * or a negative error code. */
#include <string.h>
#include <windows.h>

#include "../bic_service.h"

BIC_API double bench_request(const uint8_t *req, uint64_t req_len, uint32_t reps,
                             int32_t *status)
{
    if (req_len < SVC_REQ_HEADER)
        return -1.0;
    int kind = svc_kind(req);
    if (kind == SVC_NONE)
        return -2.0;
    uint32_t n;
    memcpy(&n, req + 4, 4);
    uint64_t total = (uint64_t)svc_bytes_per_ev(kind) * n;
    if (req_len < SVC_REQ_HEADER + total)
        return -3.0;
    for (uint64_t off = 0; off < total;) {
        size_t room;
        uint8_t *dst = svc_payload_dest(kind, n, off, &room);
        uint64_t k = total - off < room ? total - off : room;
        if (dst)
            memcpy(dst, req + SVC_REQ_HEADER + off, (size_t)k);
        off += k;
    }

    /* One solve per call, as each firmware request in the benchmark. */
    uint8_t hdr[SVC_REQ_HEADER];
    memcpy(hdr, req, SVC_REQ_HEADER);
    uint32_t one = 1;
    memcpy(hdr + 8, &one, 4);

    LARGE_INTEGER freq, t0, t1;
    QueryPerformanceFrequency(&freq);
    double best = 1e300;
    uint8_t rep[SVC_REP_HEADER];
    const double *x;
    for (uint32_t r = 0; r < reps; r++) {
        QueryPerformanceCounter(&t0);
        svc_execute(kind, hdr, rep, &x);
        QueryPerformanceCounter(&t1);
        double dt = (double)(t1.QuadPart - t0.QuadPart) / (double)freq.QuadPart;
        if (dt < best)
            best = dt;
    }
    memcpy(status, rep + 4, 4);
    return best;
}
