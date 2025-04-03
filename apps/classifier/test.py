import sys
import pandas as pd
import joblib

# 模型固定路径
MODEL_PATH = "./xgboost_model.pkl"

# 加载模型
def load_model(path):
    return joblib.load(path)

# 加载 CSV 特征数据
def load_csv(csv_file):
    df = pd.read_csv(csv_file)
    X = df.drop(columns=['sat_unsat'], errors='ignore')  # 去除目标列（如果存在）
    return X

# 预测函数
def predict(model, X):
    return model.predict(X)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("用法: python test.py [csv_path]")
        sys.exit(1)

    csv_path = sys.argv[1]

    try:
        model = load_model(MODEL_PATH)
        X = load_csv(csv_path)
        y_pred = predict(model, X)

        # 输出结果（每一行一个预测结果）
        for pred in y_pred:
            print("SAT" if int(pred) == 0 else "UNSAT")

    except Exception as e:
        print(f"[✗] 预测失败: {e}")
        sys.exit(1)
