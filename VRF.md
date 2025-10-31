VRF.GenPP(1λ):
    p ← prime exponential in λ
    G ← group of order p
    g ← generator of G
    Sample hash function F : {0, 1}* → G \ {1}
    Sample hash function F′ : {0, 1}* → Zp
    return pp ← (p, G, g, F, F′)

VRF.KeyGen(pp):
    parse pp as (p, G, g, F, F′)
    α0 ←$ Z∗p
    sk ← α0
    pk ← g^α0
    return (sk, pk)

VRF.Query(pp, sk, x):
    parse pp as (p, G, g, F, F′)
    y ← F(x)^sk
    r ←$ Zp
    c ← F′(g, F(x), g^sk, F(x)^sk, g^r, F(x)^r)
    z ← r − c·sk
    π ← (g^r, F(x)^r, z)
    return (y, π)

VRF.Verify(pp, pk, x, y, π):
    parse pp as (p, G, g, F, F′)
    ensure pk ≠ g^0
    parse π as (h1, h2, z)
    c ← F′(g, F(x), pk, y, h1, h2)
    ensure h1 = g^z · pk^c
    ensure h2 = F(x)^z · y^c
    return 1

VRF.Rotate(pp, sk, X):
    parse pp as (p, G, g, F, F′)
    α ←$ Z∗p
    sk′ ← sk · α
    pk ← g^sk
    pk′ ← g^sk′
    P ← {(VRF.Eval(sk, x), VRF.Eval(sk′, x))}x∈X
    For each (u, u′) ∈ P:
        au ← F′(u, u′, pk, pk′, P)
    y ← ∏(u,u′)∈P u^au
    y′ ← ∏(u,u′)∈P (u′)^au
    r ←$ Zp
    c ← F′(pk, y, pk′, y′, pk^r, y^r)
    z ← r − c·α
    π ← (pk^r, y^r, z)
    return (sk′, pk′, π)

VRF.VerRotate(pp, pk, pk′, P, π):
    parse pp as (p, G, g, F, F′)
    ensure pk, pk′ ≠ g^0
    For each (u, u′) ∈ P:
        au ← F′(u, u′, pk, pk′, P)
    y ← ∏(u,u′)∈P u^au
    y′ ← ∏(u,u′)∈P (u′)^au
    parse π as (h1, h2, z)
    c ← F′(pk, y, pk′, y′, h1, h2)
    ensure h1 = pk^z · (pk′)^c
    ensure h2 = y^z · (y′)^c
    return 1
