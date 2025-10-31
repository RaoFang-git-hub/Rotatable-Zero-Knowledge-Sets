OA.GenPP(1λ):
    Sample hash function H : {0, 1}* → {0, 1}λ
    return pp ← (H, λ)

OA.Init(pp):
    D ← {}
    t ← 0
    com ← (t, "")
    st ← (D, com)
    return (com, st)

OA.Update(pp, st, S = {(label1, val1), ...}):
    parse st as (D, com), com as (t, h)
    For each (label, val) ∈ S:
        ensure label ∉ D
        D[label] ← (val, t + 1)
        Add corresponding leaf to the Merkle Tree
    Recompute root hash rootHash
    com′ ← (t + 1, rootHash)
    Sort S by label as label1, ..., labeln
    C ← GetCover(root, (−∞, label1)) ∪ ... ∪ GetCover(root, (labeln, +∞))
    π ← (S, C)
    st ← (D, com′)
    return (com′, st, π)

OA.VerifyUpd(pp, com0, com1, πS):
    parse com0 as (t0, h0), com1 as (t1, h1), πS as (S, C)
    ensure t0 + 1 = t1
    if t0 = 0: ensure h0 = "" and C = {}
    ensure MergeToRootHash(C) = h0
    Let S′ = {leaf(labeli, H(Leaf, labeli, (vali, t1)))}
    ensure MergeToRootHash(S′ ∪ C) = h1
    return 1

OA.Query(pp, st, u, label):
    parse st as (D, com), com as (t, h)
    ensure u ≤ t
    if label ∈ D and D[label].epno ≤ u:
        (val, epno) ← D[label]
    else:
        (val, epno) ← (⊥, ⊥)
    Compute rootu of tree with epochs ≤ u
    π ← GetCover(rootu, (−∞, label)) ∪ GetCover(rootu, (label, +∞))
    return (π, val, epno)

OA.Verify(pp, comu, label, val, i, π):
    parse comu as (u, hashu), π as C
    if val = ⊥ or i = ⊥:
        ensure label ∉ range(C)
        ensure MergeToRootHash(C) = hashu
        return 1
    else:
        L ← node(label, H(Leaf, label, (val, i)))
        ensure i ≤ u
        ensure MergeToRootHash(C ∪ {L}) = hashu
        return 1

OA.ProveAll(pp, st, u):
    return {}

OA.VerAll(pp, comu, i, P, π):
    parse comu as (u, hashu)
    Construct S′ = {leaf(label, H(Leaf, label, (val, i))) ∀ (label, val, i) ∈ P}
    ensure labels unique and i ≤ u
    ensure MergeToRootHash(S′) = hashu
    return 1
