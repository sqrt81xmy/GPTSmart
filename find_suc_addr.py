def find_suc_addr():
    with open("./loglog.txt","r") as file:
        lines = file.readlines()
    cnt = 0
    tg = 0
    for line in lines:
        cnt += 1
        if line.startswith('processor.Execute 1uy') and '0x0012000000000000000000000000000000000231 <null> 0xf925a82b8c26520170c8d51b65a7def6364877b3' in line and '96uy; 128uy; 96uy; 64uy; 82uy; 52uy; 128uy; 21uy; 97uy; 0uy; 16uy; 87uy; 96uy;' in line:
            print(cnt)
            tg += 1
    print(tg)
find_suc_addr()
