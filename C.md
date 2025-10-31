C.Init(1λ):
    Sample hash function H : {0, 1}* → {0, 1}λ
    return (λ, H)

C.Commit(pp, m):
    aux ←$ {0, 1}λ
    c ← H(m, aux)
    return (c, aux)

C.Verify(pp, c, m, aux):
    return H(m, aux) == c
