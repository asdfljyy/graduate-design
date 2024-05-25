import random
import numpy as np
#uBlock-128：分组长度128比特，密钥K长度128比特，迭代轮数r为16
S=(7,4,9,12,11,10,13,8,15,14,1,6,0,3,2,5)#4比特S盒
S_1=(12,10,14,13,1,15,11,0,7,2,5,4,3,6,9,8)
PL=(1,3,4,6,0,2,7,5)
PL_1=(4,0,5,1,2,7,3,6)
PR=(2,7,5,0,1,6,4,3)
PR_1=(3,4,0,7,6,2,5,1)
PK=(6,0,8,13,1,15,5,10,4,9,12,2,11,3,7,14)
RC=('988cc9dd','f0e4a1b5','21357064','8397d2c6','c7d39682','4f5b1e0a','5e4a0f1b','7c682d39','392d687c','b3a7e2f6','a7b3f6e2','8e9adfcb','dcc88d99','786c293d','30246175','a1b5f0e4')#轮常数
def i2b(i):#int类型转换为32比特二进制字符串
    return bin(i)[2:].zfill(32)
def xor_32(s1,s2):#32比特十六进制字符串异或
    s1=i2b(int(s1,16))
    s2=i2b(int(s2,16))
    s=''
    size=len(s1)
    for i in range(size):
        if s1[i]==s2[i]:
            s=s+'0'
        else:
            s=s+'1'      
    s=hex(int(s,2))
    if len(s)<(2+size//4):
        s='0x'+'0'*(10-len(s))+s[2:]
    return s[2:]
def xor_64(s1,s2):#64比特十六进制字符串异或
    temp0=xor_32(s1[0:8],s2[0:8])
    temp1=xor_32(s1[8:16],s2[8:16])
    return temp0+temp1
def gen_str(n):#随机生成n比特的十六进制字符串
    res=hex(random.randint(0,2**n)).lower()
    res=res[2:]
    length=n/4
    while(len(res)<length):
        res='0'+res
    return res
def PL_128(X,pl):#64比特向量置换
    X=[X[i]+X[i+1] for i in range(0,len(X)-1,2)]
    #print('X',X)
    Y=[]
    for i in range(len(X)):
        Y.append(X[pl[i]])
    Y=''.join(Y)
    #print('Y',Y)
    return Y
def PR_128(X,pr):#64比特向量置换
    X=[X[i]+X[i+1] for i in range(0,len(X)-1,2)]
    #print('X',X)
    Y=[]
    for i in range(len(X)):
        Y.append(X[pr[i]])
    Y=''.join(Y)
    #print('Y',Y)
    return Y
def PK_128(X):#64比特向量置换
    X=list(X)
    #print('X',X)
    Y=[]
    for i in range(len(X)):
        Y.append(X[PK[i]])
    Y=''.join(Y)
    #print('Y',Y)
    return Y
def S_32(X,s):#8个4比特S盒并置，输入输出十六进制字符串
    X=list(X)
    Y=[]
    for i in range(len(X)):
        temp=s[int(X[i],16)]
        temp=hex(temp).lower()
        Y.append(temp[2])
    Y=''.join(Y)
    return Y
def S_64(X,s):#16个4比特S盒并置，输入输出十六进制字符串
    return S_32(X[0:8],s)+S_32(X[8:16],s)
def multi(x):#对二进制4比特在有限域GF(2^4)上乘2
    y=''
    if x[0]=='0':
        y=x[1:4]+'0'
    else:#溢出，左移后与0011异或(1bcd0模10011)
        if x[3]=='1':
            temp='0'
        else:
            temp='1'
        y=x[1:3]+temp+'1'
    return y
def T(X):#对十六进制32比特在有限域GF(2^4)上分块乘2
    X=i2b(int(X,16))#十六进制字符串转化为二进制字符串
    Y=''
    for i in range(8):
        #print(i,X[4*i:4*i+4],multi(X[4*i:4*i+4]))
        Y=Y+hex(int(multi(X[4*i:4*i+4]),2))[2]
    return Y
def gen_rk(K):#128比特密钥K生成128比特轮密钥RK,迭代轮数r为16
    RK=[K]#RK_0为K
    for i in range(16):
        temp=''
        #print(K[0:16],PK_128(K[0:16]))
        temp+=PK_128(K[0:16])
        temp+=xor_32(K[16:24],S_32(xor_32(temp[0:8],RC[i]),S))
        temp+=xor_32(K[24:32],T(temp[8:16]))
        K=temp[16:24]+temp[24:32]+temp[8:16]+temp[0:8]
        RK.append(K)
    return RK
def lshift_32(X,b):#64比特的X分块32比特循环左移b比特
    X0=X[0:8]
    X1=X[8:16]
    length=int(b/4)#加密算法已知，b值无需讨论
    #temp=X0[0:length]
    X0=X0[length:]+X0[0:length]
    X1=X1[length:]+X1[0:length]
    return X0+X1
def enc(X,RK):#加密，输入128比特明文和17个轮密钥
    X0=X[0:16]
    X1=X[16:32]
    for i in range(16):
        RK0=RK[i][0:16]
        RK1=RK[i][16:32]
        X0=S_64(xor_64(X0,RK0),S)
        X1=S_64(xor_64(X1,RK1),S)
        X1=xor_64(X0,X1)
        X0=xor_64(X0,lshift_32(X1,4))
        X1=xor_64(X1,lshift_32(X0,8))
        X0=xor_64(X0,lshift_32(X1,8))
        X1=xor_64(X1,lshift_32(X0,20))
        X0=xor_64(X0,X1)
        X0=PL_128(X0,PL)
        X1=PR_128(X1,PR)
    Y=xor_64(RK[16][0:16],X0)+xor_64(RK[16][16:32],X1)
    return Y
def dec(Y,RK):#解密，输入128比特密文和17个轮密钥
    Y0=Y[0:16]
    Y1=Y[16:32]
    for i in range(16):
        RK0=RK[16-i][0:16]
        RK1=RK[16-i][16:32]
        Y0=xor_64(Y0,RK0)
        Y1=xor_64(Y1,RK1)
        Y0=PL_128(Y0,PL_1)
        Y1=PR_128(Y1,PR_1)
        Y0=xor_64(Y0,Y1)
        Y1=xor_64(Y1,lshift_32(Y0,20))
        Y0=xor_64(Y0,lshift_32(Y1,8))
        Y1=xor_64(Y1,lshift_32(Y0,8))
        Y0=xor_64(Y0,lshift_32(Y1,4))
        Y1=xor_64(Y0,Y1)
        Y0=S_64(Y0,S_1)
        Y1=S_64(Y1,S_1)
    X=xor_64(RK[0][0:16],Y0)+xor_64(RK[0][16:32],Y1)
    return X
def DDT(s):#绘制4比特S盒差分分布表
    length=len(s)
    ddt=np.zeros((length,length))
    for i in range(length):
        for s_in in range(length):#遍历输入差分
            s_out=s[i]^s[i^s_in]#得到输出差分
            ddt[s_in][s_out]+=1
    return ddt
if __name__=='__main__':
    X='0123456789abcdeffedcba9876543210'
#测试样例
    K='0123456789abcdeffedcba9876543210'
    W='32122bedd023c429023470e1158c147d'
    RK=gen_rk(K)
    Y=enc(X,RK)
    Z=dec(Y,RK)
    print('测试明文：',X)
    print('测试密钥：',K)
    #print('轮密钥：',RK)
    print('加密后的密文：',Y)
    print('解密后的明文：',Z)
    if Z==X:
        print('解密成功！')
    else:
        print('解密失败！')
    if Y==W:
        print('算法实现正确！')
    else:
        print('算法实现出错！')
 ##########################################################################
    X=gen_str(128)
    K=gen_str(128)
    RK=gen_rk(K)
    Y=enc(X,RK)
    Z=dec(Y,RK)
    print('随机选取的明文：',X)
    print('随机选取的密钥：',K)
    #print('轮密钥：',RK)
    print('加密后的密文：',Y)
    print('解密后的明文：',Z)
    if Z==X:
        print('解密成功！')
    else:
        print('解密失败！')
    print('4比特S盒差分分布表：\n',DDT(S))
