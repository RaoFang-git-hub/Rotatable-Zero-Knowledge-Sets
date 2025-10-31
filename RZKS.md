RZKS.GenPP(1λ):
    ppVRF ← VRF.GenPP(1λ)
    ppOA ← OA.GenPP(1λ)
    ppC ← C.GenPP(1λ)
    ppAVC ← AVC.GenPP(1λ)
    return pp ← (ppVRF, ppOA, ppC, ppAVC)

RZKS.Init(pp):
    parse pp as (ppVRF, ppOA, ppC, ppAVC)
    epno ← 0, g ← 0
    KVRF ← {}, D ← {}, stOA ← {}, G ← {}
    sk0, pk0 ← VRF.KeyGen(ppVRF)
    KVRF[g] ← (sk0, pk0)
    G[epno] ← g
    (st′, comOA0) ← OA.Init(ppOA)
    comINT0 ← (comOA0, pk0)
    stOA[g] ← st′
    (stAVC, _) ← AVC.Init(ppAVC)
    com1, stAVC, π0 ← AVC.Update(stAVC, comINT0)
    st ← (KVRF, D, com1, epno, g, G, stOA, stAVC)
    return (com1, st)

RZKS.Update(st, Supdate):
    parse st as (KVRF, D, com, epno, g, G, stOA, stAVC)
    epno ← epno + 1
    parse Supdate as (label1, val1), ..., (labeln, valn)
    ensure all labeli distinct and not in D
    L ← {label | (label, (·)) ∈ D}
    (skg+1, pkg+1, πVRF) ← VRF.Rotate(KVRF[g], L)
    KVRF[g+1] ← (skg+1, pkg+1)
    g ← g + 1
    For g′ ∈ {g, g − 1}:
        {tlblg′_j}j∈L ← {VRF.Eval(KVRF[g′].sk, j)}j∈L
    πg−1_OA ← OA.ProveAll(stOA[g−1], epno−1)
    st′, _ ← OA.Init(ppOA)
    For i ∈ [epno−1]:
        SOA ← {(tlblg_j, tval_j) | (j, (·, i, tval_j, ·)) ∈ D}
        st′, com′_OA, _ ← OA.Update(st′, SOA)
    stOA[g] ← st′
    πg_OA ← OA.ProveAll(stOA[g], epno−1)

    SOA ← {}
    For each (labeli, vali) ∈ Supdate:
        tlbli ← VRF.Eval(KVRF[g].sk, labeli)
        (tvali, auxi) ← C.Commit(vali)
        SOA ← SOA ∪ {(tlbli, tvali)}
        D ← D ∪ {(labeli, (val, epno, tvali, auxi))}
    (stOA[g], comepno_OA, πOA) ← OA.Update(stOA[g], SOA)
    comepno_INT ← (comepno_OA, KVRF[g].pk)
    G[epno] ← g

    (com, stAVC, πAVC) ← AVC.Update(stAVC, comepno_INT)
    (_, πepno_AVC) ← AVC.Query(stAVC, t(com), t(com))
    (comepno−1_INT, πepno−1_AVC) ← AVC.Query(stAVC, t(com)−1, t(com)−1)

    π′ ← (πOA, πg−1_OA, πg_OA, πVRF, comepno−1_OA, {(tlblg−1_j, tlblg_j, tval_j, epnoj)}j∈L)
    π ← (π′, πAVC, comepno_INT, comepno−1_INT, πepno_AVC, πepno−1_AVC)
    st ← (KVRF, D, com, epno, g, G, stOA, stAVC)
    return (com, st, π)

RZKS.VerifyUpd(comt0, comt1, π):
    parse π as (π′, πAVC, comt1_INT, comt0_INT, πt1_AVC, πt0_AVC)
    parse comt0_INT as (comt0_OA, pkt0)
    parse comt1_INT as (comt1_OA, pkt1)

    ensure OA.t(comt0_OA) + 2 = AVC.t(comt0) + 1 = AVC.t(comt1) = OA.t(comt1_OA) + 1
    ensure AVC.VerExt(comt0, comt1, πAVC) = 1

    For t ∈ {t0, t1}:
        ensure AVC.Verify(comt, AVC.t(comt), comt_INT, πt_AVC) = 1

    if pkt0 = pkt1:
        parse π′ as πOA
        com′_OA ← comt0_OA
    else:
        parse π′ as (πOA, πg−1_OA, πg_OA, πVRF, com′_OA, {(tlblg−1_j, tlblg_j, tval_j, epnoj)}j∈L)
        ensure VRF.VerRotate(pkt0, pkt1, {(tlblg−1_j, tlblg_j)}j∈L, πVRF) = 1
        ensure OA.VerAll(comt0_OA, {(tlblg−1_j, tval_j, epnoj)}j∈L, πg−1_OA) = 1
        ensure OA.VerAll(com′_OA, {(tlblg_j, tval_j, epnoj)}j∈L, πg_OA) = 1

    ensure OA.VerifyUpd(com′_OA, comt1_OA, πOA) = 1
    return 1


RZKS.Query(st, u, label):
    parse st as (KVRF, D, com, epno, g, G, stOA, stAVC)
    ensure u ≤ epno

    (tlbl, πVRF) ← VRF.Query(KVRF[G[u]].sk, label)

    if label ∈ D and D[label].epnolabel ≤ u:
        (val, epnolabel, tval, aux) ← D[label]
    else:
        (val, epnolabel, tval, aux) ← (⊥, ⊥, ⊥, ⊥)

    (πOA, _) ← OA.Query(stOA[G[u]], u, tlbl)
    (πAVC, comINT) ← AVC.Query(stAVC, u, u)
    π ← (πAVC, πOA, πVRF, tlbl, tval, aux, comINT)

    return (π, val, epnolabel)

RZKS.Verify(com, label, val, t, π):
    parse π as (πAVC, πOA, πVRF, tlbl, tval, aux, comINT)
    parse comINT as (comOA, pk)

    ensure VRF.Verify(pk, label, tlbl, πVRF) = 1
    ensure AVC.t(com) = OA.t(comOA) + 1

    if t = ⊥ or val = ⊥ or tval = ⊥:
        ensure val = tval = t = ⊥
    else:
        ensure C.Verify(val, tval, aux) = 1

    ensure OA.Verify(comOA, tlbl, tval, t, πOA) = 1
    ensure AVC.Verify(com, AVC.t(com), comINT, πAVC) = 1
    return 1


RZKS.ProveExt(st, t0, t1):
    parse st as (KVRF, D, com, epno, g, G, stOA, stAVC)
    return AVC.ProveExt(stAVC, t0, t1)


RZKS.VerExt(comt0, comt1, π):
    return AVC.VerExt(comt0, comt1, π)
