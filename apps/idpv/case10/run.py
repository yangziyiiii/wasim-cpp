import subprocess
import os
from tqdm import tqdm

# 创建日志文件路径
log_file_path = "log.txt"

# 定义一个函数来运行命令并记录输出
def run_command(command):
    try:
        # 使用 subprocess.run 运行命令，捕获输出和错误
        result = subprocess.run(command, shell=True, text=True, capture_output=True)
        
        # 打开 log.txt 文件追加输出
        with open(log_file_path, "a") as log_file:
            log_file.write(f"Running command: {command}\n")
            log_file.write(f"Standard Output:\n{result.stdout}\n")
            log_file.write(f"Standard Error:\n{result.stderr}\n")
            log_file.write(f"Exit Code: {result.returncode}\n")
            log_file.write("="*50 + "\n")
        
        # 检查返回码，如果不是 0，表示有错误
        if result.returncode != 0:
            print(f"Error occurred while running command: {command}")
    except Exception as e:
        # 如果执行命令时发生任何异常，记录错误信息
        with open(log_file_path, "a") as log_file:
            log_file.write(f"Exception occurred while running command: {command}\n")
            log_file.write(str(e) + "\n")
            log_file.write("="*50 + "\n")
        print(f"Exception occurred: {e}")

# 定义要运行的命令
commands = [
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SRA_problem.btor2 30 30",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SRA_problem.btor2 30 10",
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SRAI_problem.btor2 20 20",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SRAI_problem.btor2 20 20",
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SRL_problem.btor2 20 20",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SRL_problem.btor2 20 20",
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SRLI_problem.btor2 20 20",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SRLI_problem.btor2 20 20",
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SUB_problem.btor2 20 20",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SUB_problem.btor2 20 20",
    "./test_case10 ../design/smt-sweeping/case9/ILA_Flute_SW_problem.btor2 20 20",
    "./test_case10n ../design/smt-sweeping/case9/ILA_Flute_SW_problem.btor2 20 20",
]

# 确保 log.txt 文件不存在，若存在则打开并记录输出
if not os.path.exists(log_file_path):
    with open(log_file_path, "w") as log_file:
        log_file.write("Log file created\n")

# 运行所有命令并显示进度条
for i, command in enumerate(tqdm(commands, desc="Running commands", unit="command")):
    run_command(command)

# 在后续可以继续添加新的命令到 commands 列表中