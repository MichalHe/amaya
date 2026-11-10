#ifndef SYLVAN_EXTRA_H
#define SYLVAN_EXTRA_H

#include <sylvan.h>

#ifdef __cplusplus
namespace sylvan {
    extern "C" {
#endif

#define mtbdd_uapplyp(dd, op, opid, param) CALL(mtbdd_uapplyp, dd, op, opid, param)
TASK_DECL_4(MTBDD, mtbdd_uapplyp, MTBDD, mtbdd_uapply_op, uint64_t, size_t);  // opid is 64-bit, like mtbdd_applyp's

#ifdef __cplusplus
    } // End of extern C
}
#endif

#endif
