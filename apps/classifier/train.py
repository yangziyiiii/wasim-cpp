import pandas as pd
import xgboost as xgb
from sklearn.model_selection import train_test_split, StratifiedKFold
from sklearn.metrics import accuracy_score
from xgboost import XGBClassifier
from hyperopt import fmin, tpe, hp, Trials, STATUS_OK
import glob
from tqdm import tqdm
import joblib
import matplotlib.pyplot as plt

# 获取 ./csv/ 文件夹中所有 CSV 文件的路径
csv_files = glob.glob('../csv/*.csv')


all_labels = []
df_list = []
for file in tqdm(csv_files):
    df_temp = pd.read_csv(file)
    all_labels.extend(df_temp['sat_unsat'].tolist())
    df_list.append(df_temp)

print(pd.Series(all_labels).value_counts()) #到这里是对的1 113057, 0 49821
df = pd.concat(df_list, ignore_index=True)


print(df['sat_unsat'].value_counts())


# 假设标签列为 'sat_unsat'，特征列为除 'sat_unsat' 外的所有列
X = df.drop(columns=['sat_unsat'])
y = df['sat_unsat']

# 拆分数据集为训练集和测试集，确保测试集在超参数优化和模型评估中是独立的
X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.3, random_state=42, stratify=y)

print(y_train.sum().sum())
print(y_test)
# 定义参数空间
space = {
    'max_depth': hp.choice('max_depth', range(3, 10)),
    'learning_rate': hp.uniform('learning_rate', 0.01, 0.2),
    'n_estimators': hp.choice('n_estimators', range(50, 200)),
    'subsample': hp.uniform('subsample', 0.5, 1.0),
    'colsample_bytree': hp.uniform('colsample_bytree', 0.5, 1.0)
}

# 定义目标函数
def objective(params):
    model = XGBClassifier(
        objective='binary:logistic',
        eval_metric='logloss',
        tree_method='hist',  # 使用GPU进行训练
        device='cuda',
        **params
    )
    
    # 使用K折交叉验证
    kf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
    accuracies = []
    
    for train_index, val_index in kf.split(X_train, y_train):
        X_train_fold, X_val_fold = X_train.iloc[train_index], X_train.iloc[val_index]
        y_train_fold, y_val_fold = y_train.iloc[train_index], y_train.iloc[val_index]
        
        model.fit(
            X_train_fold, y_train_fold,
            eval_set=[(X_val_fold, y_val_fold)],
            verbose=False
        )
        
        y_pred = model.predict(X_val_fold)
        accuracy = accuracy_score(y_val_fold, y_pred)
        accuracies.append(accuracy)
    
    # 返回平均准确率的负值，因为Hyperopt最小化目标
    return {'loss': -1 * sum(accuracies) / len(accuracies), 'status': STATUS_OK}

# 使用Hyperopt进行超参数优化
trials = Trials()
best = fmin(fn=objective, space=space, algo=tpe.suggest, max_evals=50, trials=trials)

# 打印最佳参数
print("Best parameters:", best)

# 使用最佳参数重新训练模型
best_model = XGBClassifier(
    base_score=0.5,
    objective='binary:logistic',
    eval_metric='logloss',
    max_depth=best['max_depth'],
    learning_rate=best['learning_rate'],
    n_estimators=best['n_estimators'],
    subsample=best['subsample'],
    colsample_bytree=best['colsample_bytree']
)

# 在整个训练集上训练模型
best_model.fit(
    X_train, y_train,
    eval_set=[(X_test, y_test)],
    verbose=True
)

# 进行预测
y_pred = best_model.predict(X_test)

# 计算准确率
accuracy = accuracy_score(y_test, y_pred)
print(f'Accuracy: {accuracy:.2f}')

joblib.dump(best_model, 'xgboost_model.pkl')
print("Model saved as 'xgboost_model.pkl'")

feature_importance = best_model.feature_importances_
feature_names = X_train.columns

# 转换为 DataFrame
feat_importance_df = pd.DataFrame({'Feature': feature_names, 'Importance': feature_importance})
feat_importance_df = feat_importance_df.sort_values(by='Importance', ascending=False)

# 绘制特征重要性条形图
feature_importance = best_model.feature_importances_
feature_names = X_train.columns

# 转换为 DataFrame
feat_importance_df = pd.DataFrame({'Feature': feature_names, 'Importance': feature_importance})
feat_importance_df = feat_importance_df.sort_values(by='Importance', ascending=False)

# 绘制特征重要性条形图
plt.figure(figsize=(10, 6))
plt.barh(feat_importance_df['Feature'][:20], feat_importance_df['Importance'][:20], color='blue')
plt.gca().invert_yaxis()  # 反转Y轴，使重要性高的特征在顶部
plt.xlabel("Feature Importance")
plt.ylabel("Feature")
plt.title("Top 20 Feature Importances in XGBoost Model")
plt.savefig('feature_importance.png')