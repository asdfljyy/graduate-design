import numpy as np
import math
import os
import time
S=(7,4,9,12,11,10,13,8,15,14,1,6,0,3,2,5)#4比特S盒
MIN_SBOXES=[0 for i in range(10)]#各轮活跃S盒数量下界
def i2b(i,n):#int类型转换为n比特二进制字符串
    return '0bin' + bin(i)[2:].zfill(n)
def MAX(alist):#求一个列表里元素最大值
    length=len(alist)
    if alist==[]:return 0
    m=alist[0]
    for i in range(length):
        if m<alist[i]:
            m=alist[i]
    return m
def DDT(s):#绘制4比特S盒差分分布表
    length=len(s)
    ddt=np.zeros((length,length))
    for i in range(length):
        for s_in in range(length):#遍历输入差分
            s_out=s[i]^s[i^s_in]#得到输出差分
            ddt[s_in][s_out]+=1
    return ddt
def createVar(f,X,n):
    return f.write('%s:BITVECTOR(%d);\n'%(X,n))
def write_cvc(Round,count):#写文件,count为猜测的活跃S盒最小数量
    #f=open(r"/home/seed/Codes/S_count/S_count_%d.cvc"%(Round),"w",encoding="utf-8")
    f=open(r"S_count_%d.cvc"%(Round),"w",encoding="utf-8")
    f.write('%定义DDT: 索引为输入差分级联输出差分\n')
    f.write('DDT:ARRAY BITVECTOR(8) OF BITVECTOR(8);\n')
    ddt=DDT(S)
    for i in range(16):
        for j in range(16):
            if ddt[i][j]>0:
                f.write('ASSERT(DDT[%s@%s]=%s);\n'%(i2b(i,4),i2b(j,4),i2b(int(4-math.log(ddt[i][j],2)),8)))
            else:
                f.write('ASSERT(DDT[%s@%s]=%s);\n'%(i2b(i,4),i2b(j,4),i2b(1,8)))
    createVar(f,'counts',8)#Round轮活跃S盒数量
    createVar(f,'PR',8)#Round轮活跃S盒相应差分概率
    for i in range(Round):#定义每轮输入输出差分,活跃S盒数量及相应差分概率,循环左移中间量
        createVar(f,'delta_in_%d'%(i),128)
        createVar(f,'delta_out_%d'%(i),128)
        createVar(f,'count_%d'%(i),8)
        createVar(f,'P_%d'%(i),8)
        createVar(f,'X1_%d_ls4'%(i),64)
        createVar(f,'X0_%d_ls8'%(i),64)
        createVar(f,'X1_%d_ls8'%(i),64)
        createVar(f,'X0_%d_ls20'%(i),64)
    for i in range(Round):
        for j in range(32):
            createVar(f,'SIN_%d_%d'%(i,j),4)#32个4比特S盒的输入
            createVar(f,'SOUT_%d_%d'%(i,j),4)#32个4比特S盒的输出
            createVar(f,'SAT_%d_%d'%(i,j),8)#活跃S盒标志
            createVar(f,'PB_%d_%d'%(i,j),8)#S盒的概率取值
    for i in range(Round):
        for j in range(5):#X0,X1经过4次变换
            createVar(f,'X0_%d_%d'%(i,j),64)
            createVar(f,'X1_%d_%d'%(i,j),64)   
    #施加约束
    f.write('ASSERT(NOT(delta_in_0=%s));\n'%(i2b(0,128)))#输入差分非零
    '''for i in range(Round):
        for j in range(32):
            f.write('ASSERT(NOT(DDT[SIN_%d_%d@SOUT_%d_%d]=0hex01));\n'%(i,j,i,j))#输入输出差分有效'''
    #每轮步骤
    for r in range(Round):
        #f.write('ASSERT(delta_in_%d=X0_%d_0@X1_%d_0);\n'%(r,r,r))
        f.write('ASSERT(delta_in_%d='%(r))
        for i in range(31):
            f.write('SIN_%d_%d@'%(r,i))
        f.write('SIN_%d_31);\n'%(r))
        #输入输出差分有效
        for i in range(32):
            f.write('ASSERT(NOT(DDT[SIN_%d_%d@SOUT_%d_%d]=0hex01));\n'%(r,i,r,i))
        #step1
        f.write('%将S盒输出划分为左右两部分\n')
        f.write('ASSERT(X0_%d_0='%(r))
        for i in range(15):
            f.write('SOUT_%d_%d@'%(r,i))
        f.write('SOUT_%d_15);\n'%(r))
        f.write('ASSERT(X1_%d_0='%(r))
        for i in range(15):
            f.write('SOUT_%d_%d@'%(r,16+i))
        f.write('SOUT_%d_31);\n'%(r))
        #step 2
        f.write('ASSERT(X1_%d_1=BVXOR(X0_%d_0,X1_%d_0));\n'%(r,r,r))
        #step 3
        f.write('ASSERT(X1_%d_ls4=X1_%d_1[59:32]@X1_%d_1[63:60]@X1_%d_1[27:0]@X1_%d_1[31:28]);\n'%(r,r,r,r,r))
        f.write('ASSERT(X0_%d_1=BVXOR(X0_%d_0,X1_%d_ls4));\n'%(r,r,r))
        #step 4
        f.write('ASSERT(X0_%d_ls8=X0_%d_1[55:32]@X0_%d_1[63:56]@X0_%d_1[23:0]@X0_%d_1[31:24]);\n'%(r,r,r,r,r))
        f.write('ASSERT(X1_%d_2=BVXOR(X1_%d_1,X0_%d_ls8));\n'%(r,r,r))
        #step 5
        f.write('ASSERT(X1_%d_ls8=X1_%d_2[55:32]@X1_%d_2[63:56]@X1_%d_2[23:0]@X1_%d_2[31:24]);\n'%(r,r,r,r,r))
        f.write('ASSERT(X0_%d_2=BVXOR(X0_%d_1,X1_%d_ls8));\n'%(r,r,r))
        #step 6
        f.write('ASSERT(X0_%d_ls20=X0_%d_2[43:32]@X0_%d_2[63:44]@X0_%d_2[11:0]@X0_%d_2[31:12]);\n'%(r,r,r,r,r))
        f.write('ASSERT(X1_%d_3=BVXOR(X1_%d_2,X0_%d_ls20));\n'%(r,r,r))
        #step 7
        f.write('ASSERT(X0_%d_3=BVXOR(X0_%d_2,X1_%d_3));\n'%(r,r,r))
        #step 8    
        f.write('ASSERT(X0_%d_4=X0_%d_3[55:48]@X0_%d_3[39:32]@X0_%d_3[31:24]@X0_%d_3[15:8]@X0_%d_3[63:56]@X0_%d_3[47:40]@X0_%d_3[7:0]@X0_%d_3[23:16]);\n'%(r,r,r,r,r,r,r,r,r))
        #step 9
        f.write('ASSERT(X1_%d_4=X1_%d_3[47:40]@X1_%d_3[7:0]@X1_%d_3[23:16]@X1_%d_3[63:56]@X1_%d_3[55:48]@X1_%d_3[15:8]@X1_%d_3[31:24]@X1_%d_3[39:32]);\n'%(r,r,r,r,r,r,r,r,r))

        f.write('ASSERT(delta_out_%d=X0_%d_4@X1_%d_4);\n'%(r,r,r))
        if r!=Round-1:#上下轮之间差分衔接
            f.write('ASSERT(delta_in_%d=delta_out_%d);\n'%(r+1,r))

    #计算活跃S盒数量及相应差分概率
    for i in range(Round):
        for j in range(32):
            f.write('ASSERT(IF SIN_%d_%d= 0hex0 THEN SAT_%d_%d= 0hex00 AND PB_%d_%d=%s ELSE SAT_%d_%d= 0hex01 AND PB_%d_%d=%s ENDIF);\n'%(i,j,i,j,i,j,i2b(0,8),i,j,i,j,'DDT[SIN_%d_%d@SOUT_%d_%d]'%(i,j,i,j)))
        f.write('ASSERT(count_%d=BVPLUS(8,'%(i))
        for k in range(31):
            f.write('SAT_%d_%d,'%(i,k))
        f.write('SAT_%d_31));\n'%(i))
        
        f.write('ASSERT(P_%d=BVPLUS(8,'%(i))
        for k in range(31):
            f.write('PB_%d_%d,'%(i,k))
        f.write('PB_%d_31));\n'%(i))
        
    if Round==1:
        f.write('ASSERT(counts=count_0);\n')
        f.write('ASSERT(PR=P_0);\n')
    else:
        f.write('ASSERT(counts=BVPLUS(8')
        for i in range(Round):
            f.write(',count_%d'%(i))
        f.write('));\n')
        
        f.write('ASSERT(PR=BVPLUS(8')
        for i in range(Round):
            f.write(',P_%d'%(i))
        f.write('));\n')
        
    f.write('ASSERT(counts=%s);\n'%(i2b(count,8)))
    
    f.write('QUERY FALSE;\n')
    f.write('COUNTEREXAMPLE;\n')
    f.close()

def process(Round):
    start=time.time()
    bound=MAX(MIN_SBOXES[0:Round-1])#此下界适用于连续运行函数的情况，运行单个函数时下界为0
    for i in range(bound+1,32*Round):
        write_cvc(Round,i)
        print(i,'stp start')
        os.system("stp S_count_%d.cvc > result_%d.txt"%(Round,Round))
        print(i,'stp finish')
        f=open(r"result_%d.txt"%(Round),"r",encoding="utf-8")
        lines=f.readlines()
        firstline=lines[0]
        #print(firstline,lines[0],type(lines[0]))
        if firstline!='Valid.\n':
            break
        #print('%s轮活跃S盒数量>'%(Round),i)
    f.close()
    S_counts=i
    MIN_SBOXES[Round-1]=i
    delta=[[ '' for i in range(2) ] for j in range(Round)]
    S_count=[ '' for i in range(Round) ]
    length=len(lines)
    for i in range(length):
        #print(len(lines[i]))
        if lines[i][8:17]=='delta_in_':
            delta[int(lines[i][17])][0]=lines[i][21:55]
        if lines[i][8:18]=='delta_out_':
            delta[int(lines[i][18])][1]=lines[i][22:56]
        if lines[i][8:14]=='count_':
            S_count[int(lines[i][14])]=int(lines[i][18:22],16)
        if lines[i][8:10]=='PR':
            P=int(lines[i][13:17],16)
    print('%s轮活跃S盒数量下界：'%(Round),S_counts)
    print('差分路径：')
    for i in range(Round):
        print('第%d轮 '%(i+1),delta[i][0],'-->',delta[i][1])
    print('相应的差分概率：2^-',P)
    print('每轮活跃S盒数量：',S_count)
    end=time.time()
    print('用时：',end-start,'s')
if __name__=='__main__':
    #process(4)
    write_cvc(4,24)
    '''for i in range(4):
        process(i+1)
    print('1--10轮活跃S盒数量下界：',MIN_SBOXES)'''
    
    
