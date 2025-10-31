import hashlib, random

class HashFunc:
    def __init__(self, lam):
        self.lam = lam
    def __call__(self, data: bytes):
        return hashlib.sha256(data).digest()

class C:
    @staticmethod
    def Init(lam: int):
        H = HashFunc(lam)
        return (lam, H)

    @staticmethod
    def Commit(pp, val):
        lam, H = pp
        if isinstance(val, str):
            val_bytes = val.encode()
        else:
            val_bytes = bytes(val)
        aux = random.getrandbits(256)
        aux_bytes = aux.to_bytes(32, "big")
        if callable(H):
            c = H(val_bytes + aux_bytes)
        else:
            c = hashlib.sha256(b'\x02' + val_bytes + aux_bytes).digest()
        return c, aux_bytes

    @staticmethod
    def Verify(pp, val, com, aux_bytes):
        lam, H = pp
        if isinstance(val, str):
            val_bytes = val.encode()
        else:
            val_bytes = bytes(val)
        if callable(H):
            return H(val_bytes + aux_bytes) == com
        else:
            return hashlib.sha256(b'\x02' + val_bytes + aux_bytes).digest() == com

# 测试部分
if __name__ == "__main__":
    pp = C.Init(256)
    val = "test_value"
    com, aux = C.Commit(pp, val)
    ok = C.Verify(pp, val, com, aux)
    print("验证结果:", ok)
    # 修改值测试错误情况
    wrong_ok = C.Verify(pp, "another_value", com, aux)
    print("错误值验证结果:", wrong_ok)
