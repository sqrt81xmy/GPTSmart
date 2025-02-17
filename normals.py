import os
import time
import subprocess
import shutil

# 定义路径
b2_directory = './B2'                                      # B2 文件夹路径
bin_directory = os.path.join(b2_directory, 'bin')        # bin 文件夹路径
abi_directory = os.path.join(b2_directory, 'abi')        # abi 文件夹路径
output_directory = os.path.join(b2_directory, 'normalFuncs')  # output 文件夹路径

# 如果 output 文件夹不存在，则创建它
if not os.path.exists(output_directory):
    os.makedirs(output_directory)

# 遍历 bin 文件夹中的每个文件
cnt = 0
for filename in os.listdir(bin_directory):
    output_file = os.path.join(output_directory, filename.replace('.bin', '_normalFuncs.txt'))
    if(os.path.exists(output_file)):
        # print("kl",cnt)
        # cnt+=1
        continue
    # else:
    #     print(filename)
    cnt+=1
    if filename.endswith('.bin'):
        bin_file = os.path.join(bin_directory, filename)  # 获取完整的 bin 文件路径
        abi_file = os.path.join(abi_directory, filename.replace('.bin', '.abi'))  # 生成对应的 abi 文件路径

        # 确保对应的 abi 文件存在
        if os.path.exists(abi_file):
            # 创建命令
            command = f"dotnet ./src/bin/Debug/net8.0/Smartian.dll fuzz -p {bin_file} -a {abi_file} -t 3600 -o output"
            print(f"Executing command: {command}")

            # 启动子进程运行命令
            process = subprocess.Popen(command, shell=True)

            # 等待 5 秒
            time.sleep(5)

            # 结束子进程
            process.terminate()
            process.wait()  # 等待进程退出

            # 检查 normalFuncs.txt 文件是否生成
            # normal_funcs_file = './normalFuncs.txt'
            # if os.path.exists(normal_funcs_file):
            #     # 生成新的文件名
            #     new_file_name = os.path.join(output_directory, f"{filename.replace('.bin', '')}_normalFuncs.txt")
            #     # 移动并重命名文件
            #     shutil.move(normal_funcs_file, new_file_name)
            #     print(f"Moved {normal_funcs_file} to {new_file_name}")
            #     time.sleep(5)
            # else:
            #     print(f"No normalFuncs.txt found after running the command for {filename}.")/home/mingyue/Smartian/EVMAnalysis/src/FrontEnd