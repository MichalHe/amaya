#include <sylvan.h>
#include <sylvan_int.h>
#include "../include/sylvan-extra.h"

TASK_IMPL_4(MTBDD, mtbdd_uapplyp, MTBDD, dd, mtbdd_uapply_op, op, size_t, opid, size_t, param) {
    sylvan_gc_test();

    MTBDD result;
    if (cache_get3(opid, dd, (size_t) op, param, &result)) {
        return result;
    }

    // WRAP will call the op with the given params. The operation id is only for caching
    // purposes and the op does not care about it.
    result = WRAP(op, dd, param);

    if (result != mtbdd_invalid) {
        cache_put3(opid, dd, (size_t) op, param, result);
        return result;
    }

    mtbddnode_t ndd = MTBDD_GETNODE(dd);
    MTBDD ddlow = node_getlow(dd, ndd);
    MTBDD ddhigh = node_gethigh(dd, ndd);

    mtbdd_refs_spawn(SPAWN(mtbdd_uapplyp, ddhigh, op, opid, param));
    MTBDD low = mtbdd_refs_push(CALL(mtbdd_uapplyp, ddlow, op, opid, param));
    MTBDD high = mtbdd_refs_sync(SYNC(mtbdd_uapplyp));
    mtbdd_refs_pop(1);
    result = mtbdd_makenode(mtbddnode_getvariable(ndd), low, high);

    cache_put3(opid, dd, (size_t)op, param, result);

    return result;
}
