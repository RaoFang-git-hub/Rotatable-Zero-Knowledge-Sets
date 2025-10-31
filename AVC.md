AVC.GenPP(1λ):
    Sample hash function H : {0, 1}* → {0, 1}λ
    return pp ← (H, λ)

AVC.Init(pp):
    D ← []
    com ← (0, "")
    st ← (D, com)
    return (com, st)

AVC.Update(pp, st, val):
    parse st as (D, com)
    D ← D || val
    Compute root hash rootHash of Merkle tree over D
    com′ ← (|D|, rootHash)
    π ← (GetCover(root, [1, t]), GetCover(root, [t + 1, t + 1]))
    st ← (D, com′)
    return (com′, st, π)

AVC.ProveExt(pp, st, t′, t):
    parse st as (D, com)
    ensure t′ < t ≤ |D|
    roott ← Merkle tree root of first t elements
    π ← (GetCover(roott, [1, t′]), GetCover(roott, [t′ + 1, t]))
    return π

AVC.VerExt(pp, com′, com, π):
    parse π as (P′, P), com′ as (t′, hash′), com as (t, hash)
    ensure range(P′) = [1, t′]
    ensure range(P′ ∪ P) = [1, t]
    ensure MergeToRootHash(P′) = hash′
    ensure MergeToRootHash(P′ ∪ P) = hash
    return 1

AVC.Query(pp, st, u, t′):
    parse st as (D, com)
    ensure u ≤ t′ ≤ |D|
    val ← D[u]
    roott′ ← Merkle tree of first t′ elements
    π ← GetCover(roott′, [1, u − 1]) ∪ GetCover(roott′, [u + 1, t′])
    return (π, val)

AVC.Verify(pp, comt′, u, val, π):
    parse comt′ as (t′, hasht′)
    L ← leaf(u, H(Leaf, u, val))
    ensure range(C ∪ {L}) = [1, t′]
    ensure MergeToRootHash(C ∪ {L}) = hasht′
    return 1
