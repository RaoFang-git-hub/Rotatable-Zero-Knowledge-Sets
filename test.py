# ============================================================
# test_rzks_alice.py — 测试 RZKS 系统基本操作流程
# ============================================================

from RZKS import RZKS  # 导入之前实现的完整系统

def main():
    print("===== [1] 系统初始化 =====")
    pp = RZKS.GenPP(256)      # 生成公共参数
    com0, st = RZKS.Init(pp)  # 初始化系统
    print("初始承诺 com0:", com0)
    print()

    print("===== [2] 添加 ('alice', 'data1') =====")
    Supdate = [("alice", "data1")]
    com1, st, π_update = RZKS.Update(st, Supdate)
    print("更新后的承诺 com1:", com1)
    print("证明 π_update 长度:", len(str(π_update)))
    print()

    print("===== [3] 查询 'alice' =====")
    π_query, val, epno = RZKS.Query(st, u=1, label="alice")
    print("查询结果 val:", val)
    print("所在 epoch:", epno)
    print()
    print(π_query)
    print("===== [4] 验证查询结果 =====")
    ok = RZKS.Verify(com1, "alice", val, epno, π_query)
    print("验证结果 (应为 True):", ok)
    print()

    print("===== [5] 测试错误数据 (应为 False) =====")
    ok_bad = RZKS.Verify(com1, "alice", "wrong_data", epno, π_query)
    print("验证结果 (应为 False):", ok_bad)
    print()

    print("===== 测试完成 =====")

if __name__ == "__main__":
    main()
