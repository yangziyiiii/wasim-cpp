import json
import networkx as nx
import pandas as pd
import os
import sys

# 加载 JSON 数据
def load_json(file_path):
    with open(file_path, 'r') as file:
        data = json.load(file)
    return data

# 将 JSON 数据转换为图，并提取额外信息
def json_to_graph(json_data):
    G = nx.DiGraph()  # 创建一个有向图，因为节点之间有明确的父子关系

    # 初始化存储额外信息的字典
    node_type_count = {'variable': 0, 'node': 0}
    node_children_count = {}
    application_count = {}

    # 获取 sat_unsat 字段的值
    # sat_unsat = json_data.get('sat_unsat', None)
    # if sat_unsat == 'SAT':
    #     sat_unsat = 0
    # elif sat_unsat == 'UNSAT':
    #     sat_unsat = 1
    # elif sat_unsat is None:
    #     raise ValueError("The 'sat_unsat' field is missing in the JSON data.")
    # else:
    #     raise ValueError(f"Invalid value for 'sat_unsat': {sat_unsat}. Expected 'SAT' or 'UNSAT'.")

    # 遍历每个节点
    for item in json_data["nodes"]:
        node_data = item["data"]
        node_id = node_data["id"]
        node_application = node_data["application"]
        node_type = node_data["type"]

        # 只传递 application 和 type 作为显式参数，其他信息通过 **node_data 传递
        node_attributes = {key: value for key, value in node_data.items() if key not in ['application', 'type']}
        G.add_node(node_id, application=node_application, type=node_type, **node_attributes)

        # 统计节点类型数量
        if node_type in node_type_count:
            node_type_count[node_type] += 1
        else:
            node_type_count[node_type] = 1
        
        # 统计应用程序类型出现的次数
        if node_application in application_count:
            application_count[node_application] += 1
        else:
            application_count[node_application] = 1

        # 如果有子节点（children_id），则添加边
        if "to" in node_data and "children_id" in node_data["to"]:
            children_ids = node_data["to"]["children_id"]
            node_children_count[node_id] = len(children_ids)  # 记录每个节点的子节点数
            for child_id in children_ids:
                G.add_edge(node_id, child_id)  # 添加边，表示父节点到子节点的关系

    return G

# 计算图的特征并保存为 CSV
def save_graph_features(G, output_path):
    # 计算图的特征
    features = {}

    # 节点和边的数量
    features['num_nodes'] = G.number_of_nodes()
    features['num_edges'] = G.number_of_edges()

    # 平均度数
    degrees = [d for n, d in G.degree()]
    features['avg_degree'] = sum(degrees) / len(degrees) if degrees else 0

    # 密度
    features['density'] = nx.density(G)

    # 平均聚类系数
    features['clustering_coefficient'] = nx.average_clustering(G)

    # 平均最短路径长度
    try:
        if nx.is_connected(G.to_undirected()):
            features['avg_shortest_path'] = nx.average_shortest_path_length(G)
        else:
            features['avg_shortest_path'] = None  # 图不连通时返回 None
    except nx.NetworkXError:
        features['avg_shortest_path'] = None  # 处理图不强连通时的异常

    # 强连通分量数量
    features['strongly_connected_components'] = len(list(nx.strongly_connected_components(G)))

    # 弱连通分量数量
    features['weakly_connected_components'] = len(list(nx.weakly_connected_components(G)))

    # 最大入度和出度
    in_degrees = [d for n, d in G.in_degree()]
    out_degrees = [d for n, d in G.out_degree()]
    features['max_in_degree'] = max(in_degrees) if in_degrees else 0
    features['max_out_degree'] = max(out_degrees) if out_degrees else 0
    features['min_in_degree'] = min(in_degrees) if in_degrees else 0
    features['min_out_degree'] = min(out_degrees) if out_degrees else 0

    # 将图的特征和 sat_unsat 标签添加到特征字典中
    # features['sat_unsat'] = sat_unsat

    # 将特征保存为 DataFrame
    features_df = pd.DataFrame([features])

    # 保存为 CSV 文件
    features_df.to_csv(output_path, index=False)

# 主程序
if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("用法: python json2graph.py [输入json文件路径] [输出csv文件路径]")
        sys.exit(1)

    input_json_path = sys.argv[1]
    output_csv_path = sys.argv[2]

    if not os.path.exists(input_json_path):
        print(f"[✗] 输入文件不存在: {input_json_path}")
        sys.exit(2)

    json_data = load_json(input_json_path)
    G = json_to_graph(json_data)
    save_graph_features(G, output_csv_path)

    print(f"[✓] Processed {input_json_path} and saved features to {output_csv_path}")