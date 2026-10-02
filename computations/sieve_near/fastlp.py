"""Active-set solver for the small dual LPs of the certificate builders (proposals only).

The case LP is  max G.x  s.t.  A x <= b, x >= 0  with few rows (m <= 12) and many
columns.  Its dual  min b.y  s.t.  A^T y >= G, y >= 0  has m variables.  We solve the
dual restricted to a working set of columns, add the most violated columns and
repeat.  Warm starts reuse the parent box's working set.  An extra row b.y >= -1
keeps the restricted problem bounded (an infeasible primal gives value -1).

Nothing here is trusted: the builders round the returned y upward to integers and
check every column inequality exactly (certificate3.check_case / certificate_out).
"""
import numpy as np
import highspy


def _restricted(A, G, b, W):
    m = A.shape[0]
    k = len(W)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    lp = highspy.HighsLp()
    lp.num_col_ = m; lp.num_row_ = k+1
    lp.col_cost_ = np.asarray(b, float); lp.col_lower_ = np.zeros(m); lp.col_upper_ = np.full(m, highspy.kHighsInf)
    M = np.vstack([A[:, W].T, np.asarray(b, float)[None, :]])
    lp.row_lower_ = np.concatenate([G[W], [-1.0]]); lp.row_upper_ = np.full(k+1, highspy.kHighsInf)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.arange(0, (k+1)*m+1, m); lp.a_matrix_.index_ = np.tile(np.arange(m), k+1)
    lp.a_matrix_.value_ = np.ascontiguousarray(M).reshape(-1)
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    sol = h.getSolution()
    return np.array(sol.col_value), np.array(sol.row_dual)[:k]


def dual_active(A, G, b, W0=None, add=12, iters=30, tol=1e-10):
    """Returns (value, y, x, W) or None.  value = b.y (>= -1), x primal on W (zeros elsewhere)."""
    A = np.asarray(A, float); G = np.asarray(G, float); b = np.asarray(b, float)
    m, n = A.shape
    W = set(int(i) for i in (W0 or []) if 0 <= i < n)
    if len(W) < m:
        ratio = G/np.maximum(A[0], 1e-300)       # far row is strictly positive on every column
        W |= set(np.argsort(-ratio)[:max(add, m)].tolist())
    scale = max(1.0, float(np.max(np.abs(G))))
    for _ in range(iters):
        Wl = sorted(W)
        r = _restricted(A, G, b, Wl)
        if r is None:
            return None
        y, xd = r
        y = np.maximum(y, 0.0)
        viol = G-A.T@y
        bad = np.where(viol > tol*scale)[0]
        if len(bad) == 0:
            x = np.zeros(n)
            x[Wl] = np.abs(xd)
            return float(np.dot(b, y)), y, x, Wl
        order = bad[np.argsort(-viol[bad])][:add]
        W |= set(order.tolist())
    return None
