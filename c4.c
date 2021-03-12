// c4.c - C in four functions

// char, int, and pointer types
// if, while, return, and expression statements
// just enough features to allow self-compilation and a bit more

// Written by Robert Swierczek

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>
// #define intMain int
#define int64 long long

char *p, *lp, // 指向source area的指针，读入的代码会以文本信息的形式读入在该区域 current position in source code
     *data;   //  data/bss 段指针 data/bss pointer

int64 *e, *le,  // 指向text area的指针，解析代码后生成相应的伪汇编代码写入该区域 current position in emitted code
    *id,      // 指向当前正在设置或解析的语义关键字结构 currently parsed identifier
    *sym,     // 指向symble area的指针，能够解析的关键字、库函数以及函数的参数和局部变量会存储在该区域 symbol table (simple list of identifiers)
    tk,       // 当前正在解析的代码的游标  current token
    ival,     // 当前解析的数字的值 current token value
    ty,       // 语义关键字结构的类型 current expression type
    loc,      // 局部变量偏移量标识 local variable offset
    line,     // 当前解析的代码行数 current line number
    src,      // 解析的代码和生成的伪汇编代码的标识 print source and assembly flag
    debug;    // 输出汇编代码执行结果标识 print executed instructions

// tokens and classes (operators last and in precedence order)
enum {
  Num = 128, Fun, Sys, Glo, Loc, Id,
  Char, Else, Enum, If, Int, Return, Sizeof, While,
  Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak
};

// opcodes
enum { LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,
       OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
       OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT };

// types
enum { CHAR, INT, PTR };

// identifier offsets (since we can't create an ident struct)
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

// 获取Token，即词法分析
void next()
{
  char *pp;

  // 只要未到文件末尾
  while (tk = *p) {
    ++p;
    if (tk == '\n') {
      // 换行符处理
      if (src) {
        printf("line %d: %.*s", line, p - lp, lp);
        lp = p;
        while (le < e) {
          printf("%8.4s", &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                           "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                           "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[*++le * 5]);
          if (*le <= ADJ) printf(" %d\n", *++le); else printf("\n");
        }
      }
      ++line;
    }
    else if (tk == '#') {
      // #符处理，此处直接忽略
      while (*p != 0 && *p != '\n') ++p;
    }
    else if ((tk >= 'a' && tk <= 'z') || (tk >= 'A' && tk <= 'Z') || tk == '_') {
      // 字符处理，变量或函数名等
      pp = p - 1;
      // 第二个字符符合变量字符范围
      while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')
        tk = tk * 147 + *p++;
      tk = (tk << 6) + (p - pp);
      id = sym;
      // 得到变量或函数名的Token，p-pp范围内的字符
      while (id[Tk]) { // 查询符号表中是否已经有该变量定义，有直接返回
        if (tk == id[Hash] && !memcmp((char *)id[Name], pp, p - pp)) { tk = id[Tk]; return; }
        id = id + Idsz;
      }
      // 符号表中没有该定义，就添加到符号表中
      id[Name] = (int64)pp;
      id[Hash] = tk;
      tk = id[Tk] = Id;
      return;
    }
    else if (tk >= '0' && tk <= '9') {
      // 数字处理
      if (ival = tk - '0') { while (*p >= '0' && *p <= '9') ival = ival * 10 + *p++ - '0'; }
      else if (*p == 'x' || *p == 'X') {
        // 十六进制数字转化为十进制
        while ((tk = *++p) && ((tk >= '0' && tk <= '9') || (tk >= 'a' && tk <= 'f') || (tk >= 'A' && tk <= 'F')))
          ival = ival * 16 + (tk & 15) + (tk >= 'A' ? 9 : 0);
      }
      else { 
        // 八进制转为十进制
        while (*p >= '0' && *p <= '7') ival = ival * 8 + *p++ - '0'; 
      }
      tk = Num;
      return;
    }
    else if (tk == '/') {
      // ‘/’字符处理
      if (*p == '/') {
        // 下一个字符也是‘/’，是注释代码，直接忽略
        ++p;
        while (*p != 0 && *p != '\n') ++p;
      }
      else {
        // 除法
        tk = Div;
        return;
      }
    }
    else if (tk == '\'' || tk == '"') {
      // 字符串处理
      pp = data;
      while (*p != 0 && *p != tk) {
        if ((ival = *p++) == '\\') {
          if ((ival = *p++) == 'n') ival = '\n';
        }
        if (tk == '"') *data++ = ival;
      }
      ++p;
      if (tk == '"') ival = (int64)pp; else tk = Num;
      return;
    }
    else if (tk == '=') { if (*p == '=') { ++p; tk = Eq; } else tk = Assign; return; }
    else if (tk == '+') { if (*p == '+') { ++p; tk = Inc; } else tk = Add; return; }
    else if (tk == '-') { if (*p == '-') { ++p; tk = Dec; } else tk = Sub; return; }
    else if (tk == '!') { if (*p == '=') { ++p; tk = Ne; } return; }
    else if (tk == '<') { if (*p == '=') { ++p; tk = Le; } else if (*p == '<') { ++p; tk = Shl; } else tk = Lt; return; }
    else if (tk == '>') { if (*p == '=') { ++p; tk = Ge; } else if (*p == '>') { ++p; tk = Shr; } else tk = Gt; return; }
    else if (tk == '|') { if (*p == '|') { ++p; tk = Lor; } else tk = Or; return; }
    else if (tk == '&') { if (*p == '&') { ++p; tk = Lan; } else tk = And; return; }
    else if (tk == '^') { tk = Xor; return; }
    else if (tk == '%') { tk = Mod; return; }
    else if (tk == '*') { tk = Mul; return; } 
    else if (tk == '[') { tk = Brak; return; }
    else if (tk == '?') { tk = Cond; return; }
    else if (tk == '~' || tk == ';' || tk == '{' || tk == '}' || tk == '(' || tk == ')' || tk == ']' || tk == ',' || tk == ':') return;
  }
}

/**
 *  操作符语义解析(如:sizof，&，|，++，--，=，==等等)
 *  生成伪汇编代码，写到text area中
 *  @param lev 操作符标识
 */
void expr(int64 lev)
{
  int64 t, *d;

  if (!tk) { printf("%d: unexpected eof in expression\n", line); exit(-1); }
  else if (tk == Num) { 
    // 数字处理，生成对应的中间代码
    *++e = IMM; *++e = ival; next(); ty = INT;
  }
  else if (tk == '"') {
    // 字符串处理
    *++e = IMM; *++e = ival; next();
    while (tk == '"') next();
      // append the end of string character '\0', all the data are default
    // to 0, so just move data one position forward.
    data = (char *)((int64)data + sizeof(int64) & -sizeof(int64)); ty = PTR;
  }
  else if (tk == Sizeof) {
    next(); if (tk == '(') next(); else { printf("%d: open paren expected in sizeof\n", line); exit(-1); }
    ty = INT; if (tk == Int) next(); else if (tk == Char) { next(); ty = CHAR; }
    while (tk == Mul) { next(); ty = ty + PTR; }
    if (tk == ')') next(); else { printf("%d: close paren expected in sizeof\n", line); exit(-1); }
    *++e = IMM; *++e = (ty == CHAR) ? sizeof(char) : sizeof(int64);
    ty = INT;
  }
  else if (tk == Id) {
    // 变量
    d = id; next();
    if (tk == '(') {
      // 函数变量，处理函数调用
      next();
      t = 0;
      // 函数参数
      while (tk != ')') { expr(Assign); *++e = PSH; ++t; if (tk == ',') next(); }
      next();
      if (d[Class] == Sys) *++e = d[Val];
      else if (d[Class] == Fun) { *++e = JSR; *++e = d[Val]; }
      else { printf("%d: bad function call\n", line); exit(-1); }
      if (t) { *++e = ADJ; *++e = t; }
      ty = d[Type];
    }
    else if (d[Class] == Num) { 
      // 处理数字
      *++e = IMM; *++e = d[Val]; ty = INT;
    }
    else {
      // 变量处理
      if (d[Class] == Loc) { *++e = LEA; *++e = loc - d[Val]; }
      else if (d[Class] == Glo) { *++e = IMM; *++e = d[Val]; }
      else { printf("%d: undefined variable\n", line); exit(-1); }
      *++e = ((ty = d[Type]) == CHAR) ? LC : LI;
    }
  }
  else if (tk == '(') {
    // 类型强转
    next();
    if (tk == Int || tk == Char) {
      t = (tk == Int) ? INT : CHAR; next();
      while (tk == Mul) { next(); t = t + PTR; }
      if (tk == ')') next(); else { printf("%d: bad cast\n", line); exit(-1); }
      expr(Inc);
      ty = t;
    }
    else {
      expr(Assign);
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    }
  }
  else if (tk == Mul) {
    // 指针取值
    next(); expr(Inc);
    if (ty > INT) ty = ty - PTR; else { printf("%d: bad dereference\n", line); exit(-1); }
    *++e = (ty == CHAR) ? LC : LI;
  }
  else if (tk == And) {
    // 取址操作
    next(); expr(Inc);
    if (*e == LC || *e == LI) --e; else { printf("%d: bad address-of\n", line); exit(-1); }
    ty = ty + PTR;
  }
  else if (tk == '!') {
    //逻辑取反
   next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = 0; *++e = EQ; ty = INT; 
 }
  else if (tk == '~') {
    // 按位取反
   next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = -1; *++e = XOR; ty = INT; 
 }
  else if (tk == Add) {
    // 正号
   next(); expr(Inc); ty = INT; }
  else if (tk == Sub) {
    // 负号
    next(); *++e = IMM;
    if (tk == Num) { *++e = -ival; next(); } else { *++e = -1; *++e = PSH; expr(Inc); *++e = MUL; }
    ty = INT;
  }
  else if (tk == Inc || tk == Dec) {
    // 自增自减
    t = tk; next(); expr(Inc);
    if (*e == LC) { *e = PSH; *++e = LC; }
    else if (*e == LI) { *e = PSH; *++e = LI; }
    else { printf("%d: bad lvalue in pre-increment\n", line); exit(-1); }
    *++e = PSH;
    *++e = IMM; *++e = (ty > PTR) ? sizeof(int64) : sizeof(char);
    *++e = (t == Inc) ? ADD : SUB;
    *++e = (ty == CHAR) ? SC : SI;
  }
  else { printf("%d: bad expression\n", line); exit(-1); }

  while (tk >= lev) { // "precedence climbing" or "Top Down Operator Precedence" method
    t = ty;
    if (tk == Assign) {
      // 赋值操作
      next();
      if (*e == LC || *e == LI) *e = PSH; else { printf("%d: bad lvalue in assignment\n", line); exit(-1); }
      expr(Assign); *++e = ((ty = t) == CHAR) ? SC : SI;
    }
    else if (tk == Cond) {
      // 三目运算符 ? : 
      next();
      *++e = BZ; d = ++e;
      expr(Assign);
      if (tk == ':') next(); else { printf("%d: conditional missing colon\n", line); exit(-1); }
      *d = (int64)(e + 3); *++e = JMP; d = ++e;
      expr(Cond);
      *d = (int64)(e + 1);
    }
    // 逻辑运算符
    else if (tk == Lor) { next(); *++e = BNZ; d = ++e; expr(Lan); *d = (int64)(e + 1); ty = INT; }
    else if (tk == Lan) { next(); *++e = BZ;  d = ++e; expr(Or);  *d = (int64)(e + 1); ty = INT; }
    else if (tk == Or)  { next(); *++e = PSH; expr(Xor); *++e = OR;  ty = INT; }
    else if (tk == Xor) { next(); *++e = PSH; expr(And); *++e = XOR; ty = INT; }
    else if (tk == And) { next(); *++e = PSH; expr(Eq);  *++e = AND; ty = INT; }
    else if (tk == Eq)  { next(); *++e = PSH; expr(Lt);  *++e = EQ;  ty = INT; }
    else if (tk == Ne)  { next(); *++e = PSH; expr(Lt);  *++e = NE;  ty = INT; }
    else if (tk == Lt)  { next(); *++e = PSH; expr(Shl); *++e = LT;  ty = INT; }
    else if (tk == Gt)  { next(); *++e = PSH; expr(Shl); *++e = GT;  ty = INT; }
    else if (tk == Le)  { next(); *++e = PSH; expr(Shl); *++e = LE;  ty = INT; }
    else if (tk == Ge)  { next(); *++e = PSH; expr(Shl); *++e = GE;  ty = INT; }
    else if (tk == Shl) { next(); *++e = PSH; expr(Add); *++e = SHL; ty = INT; }
    else if (tk == Shr) { next(); *++e = PSH; expr(Add); *++e = SHR; ty = INT; }
    // 数学运算符
    else if (tk == Add) {
      // + 
      next(); *++e = PSH; expr(Mul);
      if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64); *++e = MUL;  }
      *++e = ADD;
    }
    else if (tk == Sub) {
      // -
      next(); *++e = PSH; expr(Mul);
      if (t > PTR && t == ty) { *++e = SUB; *++e = PSH; *++e = IMM; *++e = sizeof(int64); *++e = DIV; ty = INT; }
      else if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64); *++e = MUL; *++e = SUB; }
      else *++e = SUB;
    }
    else if (tk == Mul) { 
      // * 
      next(); *++e = PSH; expr(Inc); *++e = MUL; ty = INT; 
    }
    else if (tk == Div) {
      // /
     next(); *++e = PSH; expr(Inc); *++e = DIV; ty = INT;
      }
    else if (tk == Mod) { next(); *++e = PSH; expr(Inc); *++e = MOD; ty = INT; }
    else if (tk == Inc || tk == Dec) {
      // 自增自减
      if (*e == LC) { *e = PSH; *++e = LC; }
      else if (*e == LI) { *e = PSH; *++e = LI; }
      else { printf("%d: bad lvalue in post-increment\n", line); exit(-1); }
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int64) : sizeof(char);
      *++e = (tk == Inc) ? ADD : SUB;
      *++e = (ty == CHAR) ? SC : SI;
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int64) : sizeof(char);
      *++e = (tk == Inc) ? SUB : ADD;
      next();
    }
    else if (tk == Brak) {
      // 数组取值操作
      next(); *++e = PSH; expr(Assign);
      if (tk == ']') next(); else { printf("%d: close bracket expected\n", line); exit(-1); }
      if (t > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64); *++e = MUL;  }
      else if (t < PTR) { printf("%d: pointer type expected\n", line); exit(-1); }
      *++e = ADD;
      *++e = ((ty = t - PTR) == CHAR) ? LC : LI;
    }
    else { printf("%d: compiler error tk=%d\n", line, tk); exit(-1); }
  }
}

void stmt()
{
  int64 *a, *b;
  printf("statement() token=%c \n", tk);

  if (tk == If) {
    // if语句处理
    next();
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    if (tk == Else) {
      *b = (int64)(e + 3); *++e = JMP; b = ++e;
      next();
      stmt();
    }
    *b = (int64)(e + 1);
  }
  else if (tk == While) {
    // while语句处理
    next();
    a = e + 1;
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    *++e = JMP; *++e = (int64)a;
    *b = (int64)(e + 1);
  }
  else if (tk == Return) {
    // return处理
    next();
    if (tk != ';') expr(Assign);
    *++e = LEV;
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
  else if (tk == '{') {
    // 函数体
    next();
    while (tk != '}') stmt();
    next();
  }
  else if (tk == ';') {
    next();
  }
  else {
    // 表达式处理，关键！！！
    expr(Assign);
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
}

int main(int argc, char **argv)
{
  int64 fd, bt, ty, poolsz, *idmain;
  int64 *pc, *sp, *bp, a, cycle; // vm registers
  int64 i, *t; // temps

  --argc; ++argv;
  // 命令行参数处理，s: 输出源码，d: 是否debug
  if (argc > 0 && **argv == '-' && (*argv)[1] == 's') { src = 1; --argc; ++argv; }
  if (argc > 0 && **argv == '-' && (*argv)[1] == 'd') { debug = 1; --argc; ++argv; }
  if (argc < 1) { printf("usage: c4 [-s] [-d] file ...\n"); return -1; }

  // 大家源码文件
  if ((fd = open(*argv, 0)) < 0) { printf("could not open(%s)\n", *argv); return -1; }

  poolsz = 256*1024; // arbitrary size
  // 创建符号表区
  if (!(sym = malloc(poolsz))) { printf("could not malloc(%d) symbol area\n", poolsz); return -1; }
  // 创建源代码区
  if (!(le = e = malloc(poolsz))) { printf("could not malloc(%d) text area\n", poolsz); return -1; }
  // 创建数据区
  if (!(data = malloc(poolsz))) { printf("could not malloc(%d) data area\n", poolsz); return -1; }
  // 创建栈区
  if (!(sp = malloc(poolsz))) { printf("could not malloc(%d) stack area\n", poolsz); return -1; }
  // 置内存区为0
  memset(sym,  0, poolsz);
  memset(e,    0, poolsz);
  memset(data, 0, poolsz);

  p = "char else enum if int return sizeof while "
      "open read close printf malloc free memset memcmp exit void main";

  // 添加系统关键字符号到符号表中
  i = Char; while (i <= While) { next(); id[Tk] = i++; } // add keywords to symbol table
  // 添加系统lib的方法到符号表中
  i = OPEN; while (i <= EXIT) { next(); id[Class] = Sys; id[Type] = INT; id[Val] = i++; } // add library to symbol table
  // void和main特殊处理
  next(); id[Tk] = Char; // handle void type
  next(); idmain = id; // keep track of main

  if (!(lp = p = malloc(poolsz))) { printf("could not malloc(%d) source area\n", poolsz); return -1; }
  // 读取代码源文件
  if ((i = read(fd, p, poolsz-1)) <= 0) { printf("read() returned %d\n", i); return -1; }
  // 添加结束符
  p[i] = 0;
  close(fd);

  // parse declarations
  line = 1;
  // 解析第一个token
  next();
  // 只要不是0（结束）就循环
  while (tk) {
    bt = INT; // basetype
    if (tk == Int) next();
    else if (tk == Char) { next(); bt = CHAR; }
    else if (tk == Enum) {
      // 枚举类定义
      next();
      if (tk != '{') next();
      if (tk == '{') {
        next();
        i = 0;
        while (tk != '}') {
          if (tk != Id) { printf("%d: bad enum identifier %d\n", line, tk); return -1; }
          next();
          if (tk == Assign) {
            next();
            if (tk != Num) { printf("%d: bad enum initializer\n", line); return -1; }
            i = ival;
            next();
          }
          id[Class] = Num; id[Type] = INT; id[Val] = i++;
          if (tk == ',') next();
        }
        next();
      }
    }
    while (tk != ';' && tk != '}') {
      // 一行或一个作用域内容处理
      ty = bt;
      while (tk == Mul) { next(); ty = ty + PTR; }
      // 必须是全局变量，可能是变量或方法
      if (tk != Id) { printf("%d: bad global declaration\n", line); return -1; }
      if (id[Class]) { printf("%d: duplicate global definition\n", line); return -1; }
      next();
      id[Type] = ty;
      if (tk == '(') { // function
        // 全局函数
        id[Class] = Fun;
        id[Val] = (int64)(e + 1);
        next(); i = 0;
        while (tk != ')') {
          // 函数参数处理
          ty = INT;
          if (tk == Int) next();
          else if (tk == Char) { next(); ty = CHAR; }
          while (tk == Mul) { next(); ty = ty + PTR; }
          if (tk != Id) { printf("%d: bad parameter declaration\n", line); return -1; }
          if (id[Class] == Loc) { printf("%d: duplicate parameter definition\n", line); return -1; }
          id[HClass] = id[Class]; id[Class] = Loc;
          id[HType]  = id[Type];  id[Type] = ty;
          id[HVal]   = id[Val];   id[Val] = i++;
          next();
          if (tk == ',') next();
        }
        // 函数体处理
        next();
        if (tk != '{') { printf("%d: bad function definition\n", line); return -1; }
        loc = ++i;
        next();
        while (tk == Int || tk == Char) {
          bt = (tk == Int) ? INT : CHAR;
          next();
          while (tk != ';') {
            ty = bt;
            while (tk == Mul) { next(); ty = ty + PTR; }
            if (tk != Id) { printf("%d: bad local declaration\n", line); return -1; }
            if (id[Class] == Loc) { printf("%d: duplicate local definition\n", line); return -1; }
            id[HClass] = id[Class]; id[Class] = Loc;
            id[HType]  = id[Type];  id[Type] = ty;
            id[HVal]   = id[Val];   id[Val] = ++i;
            next();
            if (tk == ',') next();
          }
          next();
        }
        *++e = ENT; *++e = i - loc;
        // 函数体处理
        while (tk != '}') stmt();
        *++e = LEV;
        id = sym; // unwind symbol table locals

        while (id[Tk]) {
          // 函数块结束，移除作用域的local变量
          if (id[Class] == Loc) {
            id[Class] = id[HClass];
            id[Type] = id[HType];
            id[Val] = id[HVal];
          }
          id = id + Idsz;
        }
      }
      else {
        // 全局变量, TODO 不支持全局变量的赋初始值，只是定义
        id[Class] = Glo;
        // 变量值保存
        id[Val] = (int64)data;
        data = data + sizeof(int64);
      }
      if (tk == ',') next();
    }
    // 下一行，或下一个作用域
    next();
  }

  if (!(pc = (int64 *)idmain[Val])) { printf("main() not defined\n"); return -1; }
  if (src) return 0;

  // setup stack
  bp = sp = (int64 *)((int64)sp + poolsz);
  *--sp = EXIT; // call exit if main returns
  *--sp = PSH; t = sp;
  *--sp = argc;
  *--sp = (int64)argv;
  *--sp = (int64)t;

  // run...，中间码执行
  cycle = 0;
  while (1) {
    i = *pc++; ++cycle;
    if (debug) {
      printf("%d> %.4s", cycle,
        &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
         "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
         "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[i * 5]);
      if (i <= ADJ) printf(" %d\n", *pc); else printf("\n");
    }
    if      (i == LEA) a = (int64)(bp + *pc++);                             // load local address
    else if (i == IMM) a = *pc++;                                         // load global address or immediate
    else if (i == JMP) pc = (int64 *)*pc;                                   // jump
    else if (i == JSR) { *--sp = (int64)(pc + 1); pc = (int64 *)*pc; }        // jump to subroutine
    else if (i == BZ)  pc = a ? pc + 1 : (int64 *)*pc;                      // branch if zero
    else if (i == BNZ) pc = a ? (int64 *)*pc : pc + 1;                      // branch if not zero
    else if (i == ENT) { *--sp = (int64)bp; bp = sp; sp = sp - *pc++; }     // enter subroutine
    else if (i == ADJ) sp = sp + *pc++;                                   // stack adjust
    else if (i == LEV) { sp = bp; bp = (int64 *)*sp++; pc = (int64 *)*sp++; } // leave subroutine
    else if (i == LI)  a = *(int64 *)a;                                     // load int
    else if (i == LC)  a = *(char *)a;                                    // load char
    else if (i == SI)  *(int64 *)*sp++ = a;                                 // store int
    else if (i == SC)  a = *(char *)*sp++ = a;                            // store char
    else if (i == PSH) *--sp = a;                                         // push

    else if (i == OR)  a = *sp++ |  a;
    else if (i == XOR) a = *sp++ ^  a;
    else if (i == AND) a = *sp++ &  a;
    else if (i == EQ)  a = *sp++ == a;
    else if (i == NE)  a = *sp++ != a;
    else if (i == LT)  a = *sp++ <  a;
    else if (i == GT)  a = *sp++ >  a;
    else if (i == LE)  a = *sp++ <= a;
    else if (i == GE)  a = *sp++ >= a;
    else if (i == SHL) a = *sp++ << a;
    else if (i == SHR) a = *sp++ >> a;
    else if (i == ADD) a = *sp++ +  a;
    else if (i == SUB) a = *sp++ -  a;
    else if (i == MUL) a = *sp++ *  a;
    else if (i == DIV) a = *sp++ /  a;
    else if (i == MOD) a = *sp++ %  a;

    else if (i == OPEN) a = open((char *)sp[1], *sp);
    else if (i == READ) a = read(sp[2], (char *)sp[1], *sp);
    else if (i == CLOS) a = close(*sp);
    else if (i == PRTF) { t = sp + pc[1]; a = printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]); }
    else if (i == MALC) a = (int64)malloc(*sp);
    else if (i == FREE) free((void *)*sp);
    else if (i == MSET) a = (int64)memset((char *)sp[2], sp[1], *sp);
    else if (i == MCMP) a = memcmp((char *)sp[2], (char *)sp[1], *sp);
    else if (i == EXIT) { printf("exit(%d) cycle = %d\n", *sp, cycle); return *sp; }
    else { printf("unknown instruction = %d! cycle = %d\n", i, cycle); return -1; }
  }
}
