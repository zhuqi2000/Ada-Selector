#!/bin/python
#coding:utf-8

"""
江煦程序智能筛选器V1.01
无界面版
编写人：朱琦
2020-4-20，更改1.00-1.01：
1）局部变量个数多统计的BUG
2）补充未加入的ADA保留字
3）将程序中未使用的函数注释，另存在参数指定的目录，原功能不变
4）建立临时目录，用于保存未注释版本，参数tarp则用于写入注释待测程序链未使用函数的文件
5）加入对同名函数的分析处理，避免引用的类型、全局变量不完整
2020-05-19,更改1.01-1.02
1）修正最终存储目录，删除多余文件操作源目录path的错误
2）解决包中protected无法识别的问题
3）纠正删除多余包程序中strPackageName的作用域BUG
2020-05-22,更改1.02-1.03
修正不能注释文件中已删除包的with语句的BUG
"""

import os
import math
import sys
import datetime
import codecs
import re
import shutil

wildcard = u"All Files(*.*)|*.*"

strInfo = u"江煦程序智能筛选器V1.01\n"  \
                      "编程实现：朱琦\n"  \
                      "软件需求：蔡陈生"


key_word = ['IF','ELIF','ELSE','END','WHILE',
            'LOOP','UNTIL','FOR','USE','AT',
            'WITH','OTHERS','RETURN',
            'AND','OR','XOR','NOT',
            'THEN','IS','IN','OUT',
            'VOLATILE','PRAGMA','DECLARE','ADDRESS',
            'PROCEDURE','FUNCTION','DO','SWITCH','CASE',
            'PACKAGE','WHEN','EXIT','BREAK',
            'CONTINUE','INLINE']
stand_type = ['UNSIGNED_8','UNSIGNED_16','UNSIGNED_32','UNSIGNED_64',
              'INTEGER','INTEGER_16','INTEGER_32','FLOAT','LONG_FLOAT',
              'LONG_LONG_INTEGER','LONG_LONG_FLOAT','CONSTANT']

stand_lib = ['interfaces','system','Ada.Numerics.Elementary_Functions',
             'Ada.Numerics.Long_Elementary_Functions']

localvar_list = []

totallines = 0
recursionCount = 0

bInRecord = False
strModule = ''
strRawModule = ''
strModuleName = ''

DictVarSymbol={}
DictFunSymbol={}
DictTypeSymbol={}

DictVarCode={}
DictFunCode={}
DictTypeCode={}

#原始格式的，用于生成新文件
DictVarCodeRaw={}
DictFunCodeRaw={}
DictTypeCodeRaw={}        
DictAdbFunCodeRaw={}

DictAdbFunSymbol={}
DictAdbFunCode={}

#同名函数代码字典
DictSameFuncCode = {}

progSymbollist = []
dependPacklist = []        
dependPackStrlist = []

calllist = []
callNumlist = []

#需要删除的包名
listNeedDelPack = []
listNeedDelFile = []

strDeclare = ''
strRawDeclare = ''

#在调用链上所有全局变量名称列表
linked_vars_list = []

#在调用链上所有类型名称列表
linked_types_list = []

def findFuncName(strline):
    #行首必须是关键字FUNCTION
    strname = ''
    if len(strline) < 9:
        #至少要大于关键字的长度，否则退出
        return strname
    
    iFinde = []
    iFinde_min = 0
    
    if strline[0:8] == 'FUNCTION':
        iFinde1 = strline.find('(')
        if iFinde1 > 8:
            iFinde.append(iFinde1)
            
        iFinde2 = strline.find('IS')
        if iFinde2 > 8:
            iFinde.append(iFinde2)

        iFinde3 = strline.find('RETURN')                
        if iFinde3 > 8:
            iFinde.append(iFinde3)

        iFinde4 = strline.find(';')                
        if iFinde4 > 8:
            iFinde.append(iFinde4)
        
        if len(iFinde) > 0:
            iFinde_min = min(iFinde)
            strname = strline[8:iFinde_min]
        else:
            strname = strline[8:]


    strname = strname.strip()

    return strname

def findProcName(strline):
    #从一行里匹配出过程名
    #行首必须是关键字PROCEDURE
    strname = ''
    if len(strline) < 10:
        #至少要大于关键字的长度，否则退出
        return strname
    
    iFinde = []
    iFinde_min = 0
    
    if strline[0:9] == 'PROCEDURE':
        iFinde1 = strline.find('(')
        if iFinde1 > 9:
            iFinde.append(iFinde1)
            
        iFinde2 = strline.find('IS')
        if iFinde2 > 9:
            iFinde.append(iFinde2)

        iFinde4 = strline.find(';')                
        if iFinde4 > 9:
            iFinde.append(iFinde4)
        
        if len(iFinde) > 0:
            iFinde_min = min(iFinde)
            strname = strline[9:iFinde_min]
        else:
            strname = strline[9:]

    strname = strname.strip()

    return strname

def findTypeName(strline):
    #从一行里匹配出类型名
    #行首必须是关键字type 或 subtype
    strname = ''
    if len(strline) < 5:
        #至少要大于关键字的长度，否则退出
        return strname
    
    iFinde = 0
    
    if strline[0:4] == 'TYPE':
        iFinde = strline.find('IS')
        strname = strline[5:iFinde]
    if strline[0:7] == 'SUBTYPE':
        iFinde = strline.find('IS')
        strname = strline[8:iFinde]

    strname = strname.strip()

    return strname

def findVarName(strline):
    global bInRecord
    #从一行里匹配出变量名
    strname = ''
    if len(strline) < 2:
        #长度至少要大于2，否则退出
        return strname
    
    iFinde = 0
    iFindR = strline.find('RECORD')
    iFindER = strline.find('END RECORD')
    iFindF = strline.find('(')
                
    if iFindER >= 0:
        bInRecord = False
    elif iFindR >= 0:
        bInRecord = True

    
    if bInRecord == False:
        iFinde = strline.find(':')
        if iFinde >= 0:
            if (iFindF > iFinde) or (iFindF < 0):
                strname = strline[:iFinde]

    strname = strname.strip()

    return strname

def findPackName(strline):
    #从一行里匹配出变量名
    strname = ''
    if len(strline) < 4:
        #长度至少要大于4，否则退出
        return strname
    
    iFinde = strline.find(';')

    if iFinde < 5:
        return strname

    if strline[0:3] == 'WITH':
        strname = strline[4:iFinde].strip()
    if strline[0:2] == 'USE':
        strname = strline[3:iFinde].strip()
    return strname

def readAdb(path):
    global totallines
    global DictAdbFunCodeRaw
    global DictAdbFunSymbol
    global DictAdbFunCode
    #同名函数代码字典{key=函数名，值=[代码1，代码2，....]}
    global DictSameFuncCode

    #读ADB文件，提取函数
    fr = codecs.open(path,'r',encoding='gbk',errors='ignore')
    iline = 0

    #处于模块内标记
    bInModule = False
    #模块名
    lastModuleName = ''
    #code字符串
    strCode = ''
    strCodeRaw = ''

    for line in fr:
        line2 = line[:]
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()
        
        #回避空行
        if len(line) == 0:
            iline = iline + 1
            continue

        #判是否还处在上次模块内部
        if bInModule:
            strCodeRaw = strCodeRaw + '\n'  + line2
            strCode = strCode + '\n' + line
            #以END 函数名收尾认为模块结束
            strEnd = 'END '+ lastModuleName
            
            if line.find(strEnd) >= 0:
                bInModule = False
                if len(lastModuleName) > 0:
                    DictSameFuncCode.setdefault(lastModuleName,[]).append(strCode)

                DictAdbFunCode[lastModuleName] = strCode
                DictAdbFunCodeRaw[lastModuleName] = strCodeRaw
        
        #提取函数
        strfun = findFuncName(line)
        if strfun != '':
            DictAdbFunSymbol[strfun] = path
            strCodeRaw = line2
            strCode = line
            
            lastModuleName = strfun                
            bInModule = True
            continue                    

        #提取过程
        strpro = findProcName(line)
        if strpro != '':
            DictAdbFunSymbol[strpro] = path
            strCode = line
            strCodeRaw = line2
            lastModuleName = strpro
            bInModule = True
            continue
        
        iline = iline + 1

    totallines = totallines + iline
        
    fr.close()

    
def readAds(path):
    global totallines
    global DictVarSymbol
    global DictFunSymbol
    global DictTypeSymbol
    global DictVarCode
    global DictFunCode
    global DictTypeCode
    global DictVarCodeRaw
    global DictFunCodeRaw
    global DictTypeCodeRaw      
    
    #读ADS文件，提取全局变量和函数
    fr = codecs.open(path,'r',encoding='gbk',errors='ignore')
    bInRecord = False
    iline = 0

    #处于模块内标记
    bInModule = False
    #半括号标记
    bHalfC = False
    #在record中
    bInRecord = False
    #模块名
    lastModuleName = ''
    #字典类型1为函数，2为类型，3为变量
    lastDictType = 1
    #code字符串
    strCode = ''
    strCodeRaw = ''
    
    for line in fr:
        line2 = line[:]
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()
        #回避空行
        if len(line) == 0:
            iline = iline + 1
            continue

        #判是否还处在上次模块内部
        if bInModule:
            strCode = strCode + '\n' + line
            strCodeRaw = strCodeRaw + '\n' + line2
            
            #上次是否半括号
            if bHalfC:
                if line.find(')') >= 0:
                    bHalfC = False
            #是否record结束
            if bInRecord:
                if line.find('END RECORD') >= 0:
                    bInRecord = False
                    
            #没有半括号，不在Record内，以分号收尾认为模块结束
            if (not bHalfC) and (not bInRecord) and (line[-1] == ';'):
                bInModule = False                
                if lastDictType == 1:
                    DictFunCode[lastModuleName] = strCode
                    DictFunCodeRaw[lastModuleName] = strCodeRaw
                    
                elif lastDictType == 2:
                    DictTypeCode[lastModuleName] = strCode
                    DictTypeCodeRaw[lastModuleName] = strCodeRaw
                    
                elif lastDictType == 3:
                    DictVarCode[lastModuleName] = strCode
                    DictVarCodeRaw[lastModuleName] = strCodeRaw

            continue
                
        #提取函数
        strfun = findFuncName(line)
        if strfun != '':
            DictFunSymbol[strfun] = path
            strCode = line
            strCodeRaw = line2
            
            lastModuleName = strfun
            lastDictType = 1
                                
            if line.find('(') > 0 and line.find(')') < 0:
                bInModule = True
                bHalfC = True
            elif line.find('(') > 0 and line.find(')') > line.find('('):
                bInModule = True
                bHalfC = False
                
            if line[-1] == ';' and bHalfC == False:
                bInModule = False
                DictFunCode[strfun] = strCode
                DictFunCodeRaw[strfun] = strCode

            continue
            
        #提取过程
        strpro = findProcName(line)
        if strpro != '':
            DictFunSymbol[strpro] = path
            strCode= line
            strCodeRaw= line2

            lastModuleName = strpro
            lastDictType = 1
            
            if line.find('(') > 0 and line.find(')') < 0:
                bInModule = True
                bHalfC = True
            elif line.find('(') > 0 and line.find(')') > line.find('('):
                bInModule = True
                bHalfC = False
                
            if line[-1] == ';' and bHalfC == False:
                bInModule = False
                DictFunCode[strpro] = strCode
                DictFunCodeRaw[strpro] = strCode
                
            continue

        #提取类型
        strtype = findTypeName(line)
        if strtype != '':
            DictTypeSymbol[strtype] = path
            strCode = line
            strCodeRaw = line2

            lastModuleName = strtype
            lastDictType = 2
            
            if line[-1] == ';':
                bInModule = False
                DictTypeCode[strtype] = strCode
                DictTypeCodeRaw[strtype] = strCodeRaw
                
            elif line.find('(') > 0 and line.find(')') < 0:
                bInModule = True
                bHalfC = True
                bInRecord = True

            else:
                bInModule = True
                bInRecord = True
                DictTypeCode[strtype] = strCode
                DictTypeCodeRaw[strtype] = strCodeRaw
                
            continue
        
        #提取全局变量
        strvar = findVarName(line)
        if strvar != '':
            DictVarSymbol[strvar] = path
            strCode = line
            strCodeRaw = line2
            

            lastModuleName = strvar
            lastDictType = 3
            
            bInModule = True
            if line[-1] == ';':
                bInModule = False
                DictVarCode[strvar] = strCode
                DictVarCodeRaw[strvar] = strCodeRaw
                
            elif line.find('(') > 0 and line.find(')') < 0:
                bInModule = True
                bHalfC = True

        iline = iline + 1

    totallines = totallines + iline
    fr.close()

def readPackage(path):
    global listNeedDelPack
    global listNeedDelFile
    #读ADS文件，提取全局变量和函数
    fr = codecs.open(path,'r',encoding='utf-8',errors='ignore')
    iline = 0
    pkgFlag = False
    bInProtected = False
    strPackageName = ''

    for line in fr:
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()
        #回避空行
        if len(line) == 0:
            continue

        #if path.find('rs422.ads') > 0:
        #    print(line)

        if pkgFlag:
            if not bInProtected:
                if line.find('END ') >= 0:
                    pkgFlag = False
                    continue
            if line.find('PROTECTED ') >= 0:
                bInProtected = True

            if line.find('TASK ') >= 0:
                bInProtected = True

            if not bInProtected:
                iline = iline + 1

            if bInProtected:
                if line.find('END ') >= 0:
                    bInProtected = False

        listline = line.split(' ')
        #去掉空项
        listline = [item for item in listline if len(item) > 0]
        if len(listline) > 1:
            if listline[0] == 'PACKAGE':
                strPackageName = listline[1]
                pkgFlag = True
                iline = 0
                #print(strPackageName)
    #print(iline)
    if iline == 0:
        #空包处理
        if len(strPackageName) > 0:
            listNeedDelPack.append(strPackageName)
            listNeedDelFile.append(path)
            adbPath = path[:-3] + 'adb'
            listNeedDelFile.append(adbPath)

    fr.close()

def isNumber(strDigit):
    #检查浮点数类型
    try:
        float(strDigit)
        return True
    except ValueError:
        pass
    #检查16进制、2进制类型
    if strDigit[:3] == '16#' or strDigit[:3] == '2#':
        return True
    
    return False
    

def AnalyzeModule(strcode,baseNum):
    global localvar_list
    global recursionCount
    global DictVarSymbol
    global DictTypeSymbol
    global DictFunSymbol
    global DictVarCode
    global DictFunCode
    global DictTypeCode
    global globalvar_count
    global localvar_count
    #同名函数代码字典{key=函数名，值=[代码1，代码2，....]}
    global DictSameFuncCode
    
    if len(strcode) == 0:
        return
    
    listline = re.split(' |\'|\.|\+|\-|\/|\-|\*|,|>|<|=|:|\(|\)|;|\n',strcode)
    #去掉空项
    listline = [item for item in listline if len(item) > 0]

    #去掉数字
    listline = [item for item in listline if not isNumber(item)]

    #去掉关键字        
    listline = [item for item in listline if item not in key_word]

    #去掉标准类型
    listline = [item for item in listline if item not in stand_type]
    
    localvar_list = []

    recursionCount = recursionCount + 1

    #提取局部变量含参数，从PROCEDURE到BEGIN中间的符号
    progSymbollist = []
    bInProg = False
    for item in listline:
        if item == 'BEGIN':
            bInProg = True
            continue

        if not bInProg:
            if item in DictTypeCode.keys():
                stritems = 'type|%s|%s'%(item,DictTypeSymbol[item])
                if not stritems in dependPackStrlist:
                    dependPackStrlist.append(stritems)
                    #递归查找变量定义依赖
                    AnalyzeDeclare(DictTypeCode[item])
            else:
                #收集函数内部局部变量
                if item not in localvar_list and item not in DictFunSymbol.keys():
                    localvar_list.append(item)
        else:
            #收集将begin后的符号，剔除本函数名和begin
            if item == 'BEGIN' or item == listline[1]:
                continue
            progSymbollist.append(item)

    if recursionCount == 1:
        localvar_count = len(localvar_list)
        #print(localvar_list)
       
    #去掉局部变量
    progSymbollist = [item for item in progSymbollist if item not in localvar_list]
    progSymbollist = [item for item in progSymbollist if item not in DictFunSymbol.keys()]
    #print(progSymbollist)
    for item in progSymbollist:            
        #检查函数依赖性
        if item in DictAdbFunCode.keys():
            #加入调用列表
            calllist.append(item)
            callNumlist.append(baseNum)
            
            stritems = 'func|%s|%s'%(item,DictAdbFunSymbol[item])
            #print(stritems)
            if not stritems in dependPackStrlist:
                dependPackStrlist.append(stritems)
                
                #递归查找下一级函数依赖
                #AnalyzeModule(DictAdbFunCode[item],baseNum + 1)       
                for func_item in DictSameFuncCode[item]:
                    AnalyzeModule(func_item,baseNum + 1)
        #检查函数声明依赖性
        if item in DictFunCode.keys():
            stritems = 'func|%s|%s'%(item,DictFunSymbol[item])
            if not stritems in dependPackStrlist:
                dependPackStrlist.append(stritems) 
                #递归查找下一级函数依赖
                AnalyzeDeclare(DictFunCode[item])                    
        #检查全局变量依赖性
        if item in DictVarCode.keys():
            if item not in linked_vars_list:
                linked_vars_list.append(item)
                
            stritems = 'vara|%s|%s'%(item,DictVarSymbol[item])
            if not stritems in dependPackStrlist:
                dependPackStrlist.append(stritems)

                if  recursionCount == 1:
                    globalvar_count = globalvar_count + 1
                #递归查找变量定义依赖
                AnalyzeDeclare(DictVarCode[item])                

def AnalyzeDeclare(strcode):
    global DictTypeCode
    global DictTypeSymbol
    global dependPackStrlist

    if len(strcode) == 0:
        return
    
    listline = re.split(' |\'|\.|\+|\-|\/|\-|\*|,|>|<|=|:|\(|\)|;|\n',strcode)
    #去掉空项
    listline = [item for item in listline if len(item) > 0]

    #去掉数字
    listline = [item for item in listline if not isNumber(item)]

    #去掉关键字        
    listline = [item for item in listline if item not in key_word]

    #去掉标准类型
    listline = [item for item in listline if item not in stand_type]
    for item in listline:
        if item in DictTypeCode:
            if item not in linked_types_list:
                linked_types_list.append(item)
            
            stritems = 'type|%s|%s'%(item,DictTypeSymbol[item])
            if not stritems in dependPackStrlist:
                dependPackStrlist.append(stritems)
                #递归查找变量定义依赖
                AnalyzeDeclare(DictTypeCode[item])

            
def ListWithedPackage(filename):
    global srcp
    #列出文件中所有引用的包文件
    fr = codecs.open(filename,'r',encoding='gbk',errors='ignore')
    for line in fr:
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()

        if len(line) == 0:
            continue

        if line.find('WITH') < 0:
            continue

        packageName = ''

        listline = line.split(';')[0].split(' ')
        listline = [item for item in listline if len(item) > 0]
        if len(listline) < 2:
            continue

        if listline[0] == 'WITH':
            packageName = listline[1].lower()
            
        adbFilename = packageName + '.adb'
        adsFilename = packageName + '.ads'
        os.chdir(srcp)
        
        #遍历目录，找到对应文件
        for fpath,dirs,fs in os.walk(srcp):
            for f in fs:
                f = f.lower()
                if f == adbFilename or f == adsFilename:
                    filepath = os.path.join(fpath,f)
                    stritems = 'pack|%s|%s'%(packageName,filepath)
                    if not stritems in dependPackStrlist:
                        dependPackStrlist.append(stritems)
                        ListWithedPackage(filepath)
        
    fr.close()

#在ads中删除不被调用到的函数声明
#在ads中删除不被引用的变量和类型
    
def delNousedFuncInAds(oldfile,newfile):
    global listCalledFuncs
    iNote = 0
    
    bInFunc = False
    glb_strfunname = 'xxxxxxxxxx'

    bInVar = False
    glb_strvarname = 'xxxxxxxxxx'

    bInType = False
    glb_strtypename = 'xxxxxxxxxx'

    bNeedDel = False
    bInRecord = False
    bInbrace = False
    infor_flag = False
    bInForRec  = False

    fw_ads = codecs.open(newfile,'w',encoding='utf-8',errors='ignore')
    #print(newfile)
    fr_ads = codecs.open(oldfile,'r',encoding='gbk',errors='ignore')
    for line in fr_ads:
        line2 = line[:]
            
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()


        if bInFunc:
            if bNeedDel:
                line2 = '--' + line2
            if bInbrace:
                pos_rightbrace = line.find(')')
                if pos_rightbrace >= 0:
                    line = line[pos_rightbrace+1:]
                    bInbrace = False
                else:
                    line =''
                                        
            if len(line) > 0:
                if line[-1] ==';':
                    bInFunc = False

        if bInType:
            if bNeedDel:
                line2 = '--' + line2
            if len(line) > 0:
                line = line.replace(';',' ; ')
                listline = line.split(' ')
                listline = [item for item in listline if len(item) > 0]
                if listline[0] =='END' and listline[1] == 'RECORD':
                    bInType = False
                    bInRecord = False
                    bNeedDel = False

        if bInVar:
            if bNeedDel:
                line2 = '--' + line2
            if len(line) > 0:
                if line[-1] ==';':
                    bInVar = False
                    bNeedDel = False

        if infor_flag:
            if bNeedDel:
                line2 = '--' + line2
            if len(line) > 0:
                linex = line.replace(';',' ; ')
                listlinex = linex.split(' ')
                listlinex = [item for item in listlinex if len(item) > 0]
                if bInForRec:
                    if listlinex[0] =='END' and listlinex[1] == 'RECORD':
                        bInForRec = False
                        infor_flag = False
                        bNeedDel = False
                else:
                    if 'RECORD' in listlinex:
                        bInForRec = True
                    else:
                        if listlinex[-1] == ';':
                            infor_flag = False
                            bNeedDel = False

        pragma_name = ''
        pos1 = 0
        pos2 = 0
        #删除与被删函数、变量和类型有关的编用
        if line.find('PRAGMA') >= 0:
            pos1 = line.find('(')
            pos2 = line.find(')')
            if pos2 > pos1 and pos1 > 0:
                pragma_name = line[pos1+1:pos2]
                
            if len(pragma_name) > 0:
                if (pragma_name not in listCalledFuncs) and (pragma_name not in linked_types_list) and (pragma_name not in linked_vars_list):               
                    line2 = '--' + line2

        for_name = ''
        pos_for =  line.find('FOR')
        pos_use = line.find('USE')
        #删除与被删类型有关的for子句
        if pos_for >= 0 and pos_use > pos_for:
            line = line.replace('\'',' \'')
            line = line.replace(';',' ;')

            listline = line.split(' ')
            listline = [item for item in listline if len(item) > 0]
            if len(listline) > 1:
                for_name = listline[1].strip()
                if len(for_name) > 0:                        
                    if (for_name not in listCalledFuncs) and (for_name not in linked_types_list) and (for_name not in linked_vars_list):                        
                        line2 = '--' + line2
                        bNeedDel = True
                    else:
                        bNeedDel= False

                    if listline[-1]!=';':
                        infor_flag = True
                        if 'RECORD' in listline:
                            bInForRec = True

                    else:
                        infor_flag = False
                    
            
        strfunname = findFuncName(line)
        if strfunname == '':
            strfunname = findProcName(line)
        
        if strfunname != '':
            bInFunc = True
            glb_strfunname = strfunname
            if strfunname not in listCalledFuncs:
                pos_leftbrace =  line.find('(')
                pos_rightbrace =  line.find(')')
                    
                if pos_leftbrace > 0 and pos_rightbrace > pos_leftbrace:
                    line = line[:pos_leftbrace] + line[pos_rightbrace + 1:]
                    bInbrace = False
                elif pos_leftbrace > 0 and pos_rightbrace < 0:
                    line = line[:pos_leftbrace]
                    bInbrace = True
                    
                line2 = '--' + line2
                bNeedDel = True
                if line[-1] == ';':
                    bInFunc = False
                    bNeedDel = False
            else:
                bNeedDel = False

        if not bInFunc:
            #匹配类型
            strtypename = findTypeName(line)
            if strtypename != '':                    
                bInType = True
                if 'RECORD' in line.split(' '):
                    bInRecord = True
                    
                glb_strtypename = strtypename
                if strtypename not in linked_types_list:
                    line2 = '--' + line2
                    bNeedDel = True
                    if line[-1] == ';':
                        bInType = False
                        bNeedDel = False
                else:
                    bNeedDel = False
                    if line[-1] == ';':
                        bInType = False
        #print(line2)    
        #匹配变量
        if (not bInFunc) and (not bInType):
            strvarname = findVarName(line)
            if strvarname != '':
                bInVar = True
                glb_strvarname = strvarname
                if strvarname not in linked_vars_list:
                    line2 = '--' + line2
                    bNeedDel = True
                    if line[-1] == ';':
                        bInVar = False
                        bNeedDel = False
                else:
                    bNeedDel = False
            


                    
        fw_ads.write(line2)
        
    fw_ads.close()
    fr_ads.close()
            
#在adb中删除不被调用到的函数体
def delNousedFuncInAdb(oldfile,newfile):
    global listCalledFuncs
    iNote = 0
    
    bInFunc = False
    bNeedDel = False
    
    glb_strfunname = 'xxxxxxxxxxx'

    fw_adb = codecs.open(newfile,'w',encoding='utf-8',errors='ignore')
    fr_adb = codecs.open(oldfile,'r',encoding='gbk',errors='ignore')
    for line in fr_adb:
        line2 = line[:]
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()

        if bInFunc:
            if bNeedDel:            
                line2 = '--' + line2
                
            if len(line) > 0:
                line = line.replace(';',' ; ')
                listline = line.split(' ')
                listline = [item for item in listline if len(item) > 0]
                if listline[0] =='END' and listline[1] == glb_strfunname:
                    bInFunc = False
                    bNeedDel = False
        
        strfunname = findFuncName(line)
        if strfunname == '':
            strfunname = findProcName(line)            
            
        if strfunname != '':
            bInFunc = True
            glb_strfunname = strfunname
            if (strfunname not in listCalledFuncs) and (strfunname!='TEST_MAIN'):
                line2 = '--' + line2
                bNeedDel = True
            else:
                bNeedDel = False
                
                
        fw_adb.write(line2)
        
    fw_adb.close()
    fr_adb.close()

#####################################################################
#在adb中删除不被调用到的函数体
def delWithInAda(oldfile,newfile):
    global listNeedDelPack
    iNote = 0
    withname = ''
    usename = ''

    fw_adb = codecs.open(newfile,'w',encoding='utf-8',errors='ignore')
    fr_adb = codecs.open(oldfile,'r',encoding='utf-8',errors='ignore')
    for line in fr_adb:
        line2 = line[:]
        #删除注释
        iNote = line.find('--')
        if iNote > 0:
            line = line[:iNote]
        elif iNote == 0:
            line = ''
            
        line = line.strip()
        line = line.upper()
        line = line.replace(';',' ;')
       
        listline = line.split(' ')
        listline = [item for item in listline if len(item) > 0]
        bNoteit = False
        if len(listline) > 0:
            for i in range(len(listline)):
                if listline[i] == 'WITH' and i+1 < len(listline):
                    withname = listline[i+1]
                    if withname in listNeedDelPack:
                        bNoteit = True

                if listline[i] == 'USE' and i+1 < len(listline):
                    usename = listline[i+1]
                    if usename in listNeedDelPack:
                        bNoteit = True
        if bNoteit:
            line2 = '--' + line2

        fw_adb.write(line2)
        
    fw_adb.close()
    fr_adb.close()

#####################################################################
#主程序入口,构建全局字典
para_list = sys.argv[1:]
lang = 'ADA'
func = 'Cross_Product_Vector31'
tarp = 'D:\\work\\js'
srcp = 'D:\\work\\src'

for i in para_list:
    if len(i) > 5:
        if i[0:5] == 'lang=':
            lang = i[5:].strip().upper()
        elif i[0:5] == 'func=':
            func = i[5:].strip().upper()
        elif i[0:5] == 'srcp=':
            srcp = i[5:].strip()
        elif i[0:5] == 'tarp=':
            tarp = i[5:].strip()
        else:
            print('\n参数选项不存在')        
    else:
        print('\n参数格式错误')
        
os.chdir(srcp)

#从参数中获取源目录
#path = srcp
#区分Ada或C，目前版本只实现Ada
if lang == 'ADA':
    #遍历创建符号字典
    for fpath,dirs,fs in os.walk(srcp):
        for f in fs:
            lenFilename = len(f)
            if lenFilename < 5:
                continue
            suffix = f[lenFilename - 3:]
            if suffix == 'ads':
                readAds(os.path.join(fpath,f))
            elif suffix == 'adb':
                readAdb(os.path.join(fpath,f))
                
    print(u'\n符号字典构建完成')

###########################################################
recursionCount = 0
globalvar_count = 0
localvar_count = 0

#函数调用列表
calllist = []
#函数调用者序号列表
callNumlist = []
#调用者序号
baseNum = 0

#查找指定函数
#从参数中获取待测函数
strname = func
strname = strname.upper()
if strname != '':
    #第一级匹配，首先在adb找自己代码
    if strname in DictAdbFunCode.keys():
        dependPacklist.append(strname)
        stritems = 'func|%s|%s'%(strname,DictAdbFunSymbol[strname])
        dependPackStrlist.append(stritems)

        #加入调用列表
        calllist.append(strname)
        callNumlist.append(0)
        
        #分析指定模块代码
        #AnalyzeModule(DictAdbFunCode[strname],0)
        #如果有同名，需要扫描所有同名函数的代码
        for item in DictSameFuncCode[strname]:
            AnalyzeModule(item,0)

        #分析with依赖包
        adbFilename = DictAdbFunSymbol[strname]
        packname = adbFilename.split('\\')[-1].split('.')[0]
        adsFilename = adbFilename.replace('.adb','.ads')
                        
        ListWithedPackage(adbFilename)
        ListWithedPackage(adsFilename)

        stritems = 'pack|%s|%s'%(packname,adsFilename)
        if not stritems in dependPackStrlist:
            dependPackStrlist.append(stritems)

    #对函数进行静态分析
    #1、目录内所有源程序的总行数
    strLineInfo = u'\n所有源程序总行数：%d' %totallines
    print(strLineInfo)

    #2、指定模块的行数
    if strname in DictAdbFunCode.keys():
        linecount = len(DictAdbFunCode[strname].split('\n'))
        rawlinecount = len(DictAdbFunCodeRaw[strname].split('\n'))            
        strLineInfo = u'\n函数%s有效行数：%d' %(strname,linecount)
        print(strLineInfo)


    #3、局部变量个数
    strLineInfo = u'\n函数中局部变量（含参数）个数：%d' %localvar_count
    print(strLineInfo)

    #4、全局变量个数
    strLineInfo = u'\n函数中全局变量个数：%d' %globalvar_count
    print(strLineInfo)

    #5、循环调用检查
    bLoopcalled = False
    curCallNum = 99
    if len(calllist)  > 1:
        for i in range(len(calllist) - 1,-1,-1):
            for j in range(len(calllist) - 2,-1,-1):                        
                if calllist[i] == calllist[j]:
                    curCallNum = callNumlist[i]
                    while curCallNum > 0:
                        if curCallNum == j:                                
                            strLineInfo = u'\n函数中存在循环调用：%s' %calllist[i]
                            break
                        curCallNum = callNumlist[curCallNum]
                else:
                    strLineInfo = u'\n函数中无循环调用'
    else:
        strLineInfo = u'\n函数中无循环调用'
    print(strLineInfo)

    #6、同名函数分析
    if len(DictSameFuncCode[strname]) > 1:
        num_samefunc = len(DictSameFuncCode[strname])
        strLineInfo = u'\n函数存在%d个同名函数' %num_samefunc
        print(strLineInfo)
###################################################################################        
#从参数中获取目的目录
#新建一个临时目录
#path = tarp + '\\'
if not os.path.isdir(tarp):
    os.mkdir(tarp)
else:
    filelist = os.listdir(tarp)
    for f in filelist:
        filepath = os.path.join(tarp,f)
        if os.path.isfile(filepath):
            os.remove(filepath)

path = tarp + '\\temp\\'
if not os.path.isdir(path):
    os.mkdir(path)
else:
    filelist = os.listdir(path)
    for f in filelist:
        filepath = os.path.join(path,f)
        if os.path.isfile(filepath):
            os.remove(filepath)

os.chdir(path)
#复制依赖文件
for item in dependPackStrlist:
    srcfilename = item.split('|')[2]
    filename = srcfilename.split('\\')[-1]
    tarfilename = path + filename
    shutil.copy(srcfilename,tarfilename)

#从参数中获取需要测试的函数
strname = func.upper()
if strname in DictAdbFunSymbol.keys():
    #根据文件名得到包名
    packname = DictAdbFunSymbol[strname].split('\\')[-1].split('.')[0]
    packname = packname.replace('-','.');
    #生成一个测试主程序，命名为test_main.adb，调用被测函数
    filename = path + 'test_main.adb'
    #分析函数声明，提取形参
    strFunDec = DictFunCode[strname]
    strFunDec = strFunDec.replace('\n','')
    strFunDec.strip()
    ipos1 = strFunDec.find('(')
    ipos2 = strFunDec.find(')')
    ipos3 =  strFunDec.find('RETURN')

    retType = ''
    retTypePack = ''

    #如果存在返回值，提取返回值类型
    if ipos3 > 0:
        retType = strFunDec.split('RETURN')[-1].replace(';','')
        retType = retType.strip()
        fpath = DictTypeSymbol[retType]
        fname = fpath.split('\\')[-1].split('.')[0]
        retTypePack = fname

    #提取每个形参的类型
    listLineParaType = []
    listParaTypeFile = []
    if ipos1 > 0 and ipos2 > ipos1 + 1:
        strLinePara = strFunDec[ipos1+1:ipos2]
        listLinePara = strLinePara.split(';')
        for i in listLinePara:
            strParam = i.split(':')[1].upper()
            strParam = strParam.replace('IN','')
            strParam = strParam.replace('OUT','')
            strParam = strParam.strip()
            listLineParaType.append(strParam)
        #根据形参类型匹配库文件
        for i in listLineParaType:
            if i in DictTypeSymbol.keys():
                fpath = DictTypeSymbol[i]
                fname = fpath.split('\\')[-1].split('.')[0]
                if not fname in listParaTypeFile:
                    listParaTypeFile.append(fname);

        if not retTypePack in listParaTypeFile:
            listParaTypeFile.append(retTypePack);

    #参数引入
    #strParam = textParam.GetValue().strip()
    #print(filename)
    with open(filename,'w') as fw:
        #引用系统库文件
        fw.write('with interfaces;\nuse interfaces;\n')
        fw.write('with system;\nuse system;\n')
        fw.write('with Ada.Numerics.Elementary_Functions;\nuse Ada.Numerics.Elementary_Functions;\n')
        fw.write('with Ada.Numerics.Long_Elementary_Functions;\nuse Ada.Numerics.Long_Elementary_Functions;\n')
        #引用参数需要用到的文件
        for item in listParaTypeFile:
            if len(item) > 0:
                item = item.replace('-','.')
                fw.write('with ')
                fw.write(item)
                fw.write(';\n')
                fw.write('use ')
                fw.write(item)
                fw.write(';\n')

        #引用被测包文件
        fw.write('with ')
        fw.write(packname)
        fw.write(';\n')
        fw.write('use ')
        fw.write(packname)
        fw.write(';\n')
        fw.write('procedure test_main is\n')
        #定义参数
        strparam = 'param_'
        listVar = []
        i = 1
        for item in listLineParaType:
            strparam = 'param_%d'%i
            listVar.append(strparam)
            i=i+1
            fw.write('    '+strparam)
            fw.write(':')
            fw.write(item)
            fw.write(';\n')

        if retType != '':
            fw.write('    ret : ')
            fw.write(retType)
            fw.write(';\n')
            
        fw.write('begin\n    ')
        if retType != '':
            fw.write('ret := ')

        fw.write(strname)
        if len(listVar) > 0:
            fw.write('(')
            i = 0
            for item in listVar:
                fw.write(item)
                if i < len(listVar) - 1:
                    fw.write(',')
                i = i + 1
            fw.write(')')
            
        fw.write(';\n')                
        fw.write('end test_main;')

#列出调用过的函数
listCalledFuncs = []
for item in dependPackStrlist:
    listitem = item.split('|')
    if len(listitem) >= 3:
        if listitem[0] == 'func':
            funname = listitem[1]
            listCalledFuncs.append(funname)

#对文件进行缩略处理，注释不被调用的函数
#newpath = tarp
path = tarp + '\\temp\\'
if not os.path.exists(path):
    os.makedirs(path)

newpath = tarp + '\\comp\\'
newfile = ''
if not os.path.exists(newpath):
    os.makedirs(newpath)
else:
    filelist = os.listdir(newpath)
    for f in filelist:
        filepath = os.path.join(newpath,f)
        if os.path.isfile(filepath):
            os.remove(filepath)

#遍历path下的所有adb\ads文件
for fpath,dirs,fs in os.walk(path):
    for f in fs:
        lenFilename = len(f)
        if lenFilename < 5:
            continue
        suffix = f[lenFilename - 3:]
        newfile = newpath + '\\' + f
        #print(newfile)
        if suffix == 'ads':
            delNousedFuncInAds(os.path.join(fpath,f),newfile)
        elif suffix == 'adb':
            delNousedFuncInAdb(os.path.join(fpath,f),newfile)

path = tarp + '\\comp\\'
if not os.path.exists(path):
    os.makedirs(path)

#空包检查
for fpath,dirs,fs in os.walk(path):
    for f in fs:
        lenFilename = len(f)
        if lenFilename < 5:
            continue
        suffix = f[lenFilename - 3:]
        newfile = newpath + '\\' + f
        #print(newfile)
        if suffix == 'ads':
            readPackage(os.path.join(fpath,f))

#print(listNeedDelFile)
#删除空包
for itemfile in listNeedDelFile:
    if os.path.exists(itemfile):
        os.remove(itemfile)

path = tarp + '\\comp\\'
if not os.path.exists(path):
    os.makedirs(path)

#复制到目的路径
newpath = tarp
newfile = ''
if not os.path.exists(newpath):
    os.makedirs(newpath)
else:
    filelist = os.listdir(newpath)
    for f in filelist:
        filepath = os.path.join(newpath,f)
        if os.path.isfile(filepath):
            os.remove(filepath)

#遍历path下的所有adb\ads文件
for fpath,dirs,fs in os.walk(path):
    for f in fs:
        lenFilename = len(f)
        if lenFilename < 5:
            continue
        suffix = f[lenFilename - 3:]
        newfile = newpath + '\\' + f
        #print(newfile)
        if suffix == 'ads' or suffix == 'adb':
            delWithInAda(os.path.join(fpath,f),newfile)

#删除临时文件、目录
os.chdir(tarp)
shutil.rmtree(tarp + '\\temp')
shutil.rmtree(tarp + '\\comp')


