/* A tiny BASIC interpreter */

#include <string.h>
#include <stdio.h>
#include <setjmp.h>
#include <math.h>
#include <ctype.h>
#include <stdlib.h>

#define NUM_LAB   100
#define LAB_LEN   10
#define LOOP_NEST 25
#define SUB_NEST  25
#define PROG_SIZE 10000

#define DELIMITER 1
#define VARIABLE  2
#define NUMBER    3
#define COMMAND   4
#define STRING    5
#define QUOTE     6

#define NEXT      1
#define IF        2
#define ENDIF     3
#define FOR       4
#define TO        5
#define ELSE      6
#define WHILE     7
#define WEND      8
#define BREAK     9
#define CONTINUE  10
#define PRINT     11
#define GOTO      12
#define GOSUB     13
#define RETURN    14
#define INPUT     15
#define END       16
#define EOL       17
#define FINISHED  18

char *prog;  /* holds expression to be analyzed */
jmp_buf e_buf; /* hold environment for longjmp() */

int variables[26]= {    /* 26 user variables,  A-Z */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0
};

struct commands { /* keyword lookup table */
  char command[20];
  char tok;
} table[] = { /* Commands must be entered lowercase */
  "next",   NEXT, /* in this table. */
  "if",     IF,
  "endif",  ENDIF,
  "for",    FOR,
  "to",     TO,
  "else",   ELSE,
  "while",  WHILE,
  "wend",   WEND,
  "break",  BREAK,
  "continue", CONTINUE,
  "print",  PRINT,
  "goto",   GOTO,
  "gosub",  GOSUB,
  "return", RETURN,
  "input",  INPUT,
  "end",    END,
  "",       END  /* mark end of table */
};

char token[80];
char token_type, tok;

struct label {
  char *p;  /* points to place to go in source file*/
  int name;
} label_table[NUM_LAB];

struct loop_stack {
  int var;     /* counter variable */
  int target;  /* target value */
  char *beginLoc; /* top of loop */
  char *endLoc;
  char *breakLoc;
} lstack[LOOP_NEST]; /* stack for FOR/NEXT loop */

char *gstack[SUB_NEST]; /* stack for gosub */

int ltos;  /* index to top of FOR stack */
int gtos;  /* index to top of GOSUB stack */

/**************************************/
/************* utility ****************/
/**************************************/

/* Load a program. */
int load_program(char *p, char *fname)
{
  FILE *fp;
  int i=0;
  int notInQuote = 1;

  if(!(fp=fopen(fname, "rb"))) return 0;

  i = 0;
  do {
    *p = getc(fp);
    if (*p == '"')
      notInQuote = 1 - notInQuote;
    if (notInQuote) 
      *p = tolower(*p);
    ++p;
    ++i;
  } while(!feof(fp) && i<PROG_SIZE);
  *(p-2) = '\0'; /* null terminate the program */
  fclose(fp);
  return 1;
}

/* display an error message */
void serror(int error)
{
  static char *e[]= {
    "syntax error",
    "unbalanced parentheses",
    "no expression present",
    "equals sign expected",
    "not a variable",
    "Label table full",
    "duplicate label",
    "undefined label",
    "improper loop nest",
    "TO expected",
    "too many nested FOR loops",
    "NEXT without FOR",
    "too many nested GOSUBs",
    "RETURN without GOSUB"
  };
  printf("%s\n", e[error]);
  longjmp(e_buf, 1); /* return to save point */
}

/***********************************/
/************** lexer **************/
/***********************************/

static char *lastTokPos;

int iswhite(char c)
{
  return ((c == ' ' || c == '\t') ? 1 : 0) ;
}

/* Return true if c is a delimiter. */
int isdelim(char c)
{
   return ((strchr(" ;,+-<>/*%^=()", c) || c==9 || c=='\n' || c==0) ? 1 : 0) ;
}

/* Look up a a token's internal representation in the
   token table.
*/
int look_up(char *s)
{
  int i;

  /* see if token is in table */
  for(i=0; *table[i].command; ++i)
      if(!strcmp(table[i].command, s))
         return table[i].tok;

  return 0; /* unknown command */
}

/* Get a token. */
int get_token()
{
  char *temp;

  token_type=0; tok=0;
  temp=token;
  lastTokPos = prog; /* to capture FINISHED token */

  if(*prog == '\0') { /* end of file */
    *token=0;
    tok = FINISHED;
    return(token_type=DELIMITER);
  }

  while(iswhite(*prog)) ++prog;  /* skip over white space */

  lastTokPos = prog ; /* more aggressive position */

  if(*prog == '\n') { /* newline */
    ++prog;
    tok = EOL; *token='\n';
    token[1]=0;
    return (token_type = DELIMITER);
  }

  if(strchr("+-*^/%=;(),><", *prog)){ /* delimiter */
    *temp++ = *prog++;
    *temp=0;
    return (token_type=DELIMITER);
  }

  if(*prog == '"') { /* quoted string */
    ++prog;
    while((*prog != '"') && (*prog != '\n'))
       *temp++ = *prog++;
    if(*prog=='\n')
       serror(1);
    ++prog;
    *temp=0;
    return(token_type=QUOTE);
  }

  if(isdigit(*prog)) { /* number */
    while(isdigit(*prog))
       *temp++ = *prog++;
    *temp = '\0';
    return(token_type = NUMBER);
  }

  if(islower(*prog)) { /* var or command */
    while(!isdelim(*prog))
       *temp++ = *prog++;
    token_type=STRING;
  }

  *temp = '\0';

  /* see if a string is a command or a variable */
  if(token_type==STRING) {
    tok = look_up(token); /* convert to internal rep */
    if(!tok)
       token_type = VARIABLE;
    else
       token_type = COMMAND; /* is a command */
  }
  return token_type;
}

/* Return a token to input stream. */
void putback()
{
  prog = lastTokPos;
}

/* Find the start of the next line. */
void find_eol()
{
  while(*prog != '\n' && *prog!='\0')
     ++prog;
  if(*prog)
     ++prog;
}

/*****************************************/
/************ label management ***********/
/*****************************************/

/* Initialize the array that holds the labels.
   By convention, a null label name indicates that
   array position is unused.
*/
void label_init()
{
  int t;

  for(t=0; t<NUM_LAB; ++t) label_table[t].name=0;
}

/* Return index of next free position in label array.
   A -1 is returned if the array is full.
   A -2 is returned when duplicate label is found.
*/
int get_next_label(int name)
{
  int t;

  for(t=0;t<NUM_LAB;++t) {
    if(label_table[t].name==0)
       return t;

    if(label_table[t].name == name)
       return -2; /* dup */
  }

  return -1;
}

/* Find location of given label.  A null is returned if
   label is not found; otherwise a pointer to the position
   of the label is returned.
*/
char *find_label(int name)
{
  int t;

  for(t=0; t<NUM_LAB; ++t)
    if(label_table[t].name == name)
       return label_table[t].p;

  return 0; /* error condition */
}

/* Find all labels. */
void scan_labels()
{
  int addr;
  char *temp;

  label_init();  /* zero all labels */
  temp = prog;   /* save pointer to top of program */

  /* a label is an integer at the beginning of the line */
  do {
    get_token();
    if(token_type==NUMBER) {
      int name = atoi(token) ;
      addr = ((name == 0) ? -2 : get_next_label(name));
      if(addr < 0) {
          (addr==-1) ? serror(5) : serror(6);
      }
      label_table[addr].name = name;
      label_table[addr].p = prog;  /* current point in program */
    }
    /* if not on a blank line, find next line */
    if(tok!=EOL)
       find_eol();
  } while(tok!=FINISHED);
  prog = temp;  /* restore to original */
}

/***************************************************/
/**************** Expression parser ****************/
/***************************************************/

/* Find value of number or variable. */
void primitive(int *result)
{
  switch(token_type) {
  case VARIABLE:
    *result = variables[*token-'a'];
    get_token();
    return;
  case NUMBER:
    *result = atoi(token);
    get_token();
    return;
  default:
    serror(0);
  }
}

void level2(int *result) ;

/* Process parenthesized expression. */
void level6(int *result)
{
  if(*token == '(') {
    get_token();
    level2(result);
    if(*token != ')')
      serror(1);
    get_token();
  }
  else
    primitive(result);
}

/* Reverse the sign. */
void unary(char o, int *r)
{
  if(o == '-')
    *r = -(*r);
}

/* Is a unary + or -. */
void level5(int *result)
{
  char op = 0;

  if(*token=='+' || *token=='-') {
    op = *token;
    get_token();
  }
  level6(result);
  if(op)
    unary(op, result);
}

/* Perform the specified arithmetic. */
void arith(char o, int *r, int *h)
{
  int t, ex;

  switch(o) {
    case '-':
      *r = *r-*h;
      break;
    case '+':
      *r = *r+*h;
      break;
    case '*':
      *r = *r * *h;
      break;
    case '/':
      *r = (*r)/(*h);
      break;
    case '%':
      t = (*r)/(*h);
      *r = *r-(t*(*h));
      break;
    case '^':
      ex = *r;
      if(*h==0) {
        *r = 1;
        break;
      }
      for(t=*h-1; t>0; --t) *r = (*r) * ex;
      break;
  }
}

/* Process integer exponent. */
void level4(int *result)
{
  int hold;

  level5(result);
  if(*token== '^') {
    get_token();
    level4(&hold);
    arith('^', result, &hold);
  }
}

/* Multiply or divide two factors. */
void level3(int *result)
{
  char  op;
  int hold;

  level4(result);
  while((op = *token) == '*' || op == '/' || op == '%') {
    get_token();
    level4(&hold);
    arith(op, result, &hold);
  }
}

/*  Add or subtract two terms. */
void level2(int *result)
{
  char  op;
  int hold;

  level3(result);
  while((op = *token) == '+' || op == '-') {
    get_token();
    level3(&hold);
    arith(op, result, &hold);
  }
}

/* Entry point into parser. */
void get_exp(int *result)
{
  get_token();
  if(!*token) {
    serror(2);
    return;
  }
  level2(result);
  putback(); /* return last token read to input stream */
}

/* Assign a variable a value. */
void assignment()
{
  int var, value;

  /* token contains variable name */
  var = *token-'a';

  /* get the equals sign */
  get_token();
  if(*token != '=') {
    serror(3);
  }

  /* get the value to assign to var */
  get_exp(&value);

  /* assign the value */
  variables[var] = value;
}

/****************************************/
/********* statement parsers ************/
/****************************************/

void exit_block(const char *msg, int beginTok, int endTok)
{
  int blockScope = 1 ;
  while (blockScope > 0) {
    if (tok == endTok) {
      if (--blockScope == 0) {
        break ;
      }
    }
    else if (tok == beginTok) {
      ++blockScope ;
    }
    else if (tok == FINISHED) {
      printf("%s not properly terminated ", msg) ;
      serror(3) ;
    }
    get_token();
  }
  /* scanner 'token' now points at endTok, and prog points after endTok */
}

/************* print **********/

/* Execute a simple version of the BASIC PRINT statement */
void print()
{
  int answer;
  int len=0, spaces;
  char last_delim;

  do {
    get_token(); /* get next list item */
    if(tok==EOL || tok==FINISHED) break;
    if(token_type==QUOTE) { /* is string */
      printf(token);
      len += strlen(token);
      get_token();
    }
    else { /* is expression */
      putback();
      get_exp(&answer);
      get_token();
      len += printf("%d", answer);
    }
    last_delim = *token;

    if(*token==';') {
      /* compute number of spaces to move to next tab */
      spaces = 8 - (len % 8);
      len += spaces; /* add in the tabbing position */
      while(spaces) {
        printf(" ");
        spaces--;
      }
    }
    else if(*token==',') /* do nothing */;
    else if(tok!=EOL && tok!=FINISHED) serror(0);
  } while (*token==';' || *token==',');

  if(tok==EOL || tok==FINISHED) {
    if(last_delim != ';' && last_delim!=',') printf("\n");
  }
  else serror(0); /* error is not , or ; */

}

/************* goto **********/

/* Execute a computed GOTO statement. */
void exec_goto()
{
  char *loc;
  int value;

  get_exp(&value);
  loc = find_label(value);
  if(loc == 0)
    serror(7); /* label not defined */

  else prog=loc;  /* start program running at that loc */
}

/************* if **********/

/* Execute an IF statement. */
void exec_if()
{
  int x , y, cond;
  char op;

  get_exp(&x); /* get left expression */

  get_token(); /* get the operator */
  if(!strchr("=<>", *token)) {
    serror(0); /* not a legal operator */
    return;
  }
  op=*token;

  get_exp(&y); /* get right expression */

  /* determine the outcome */
  cond = 0;
  switch(op) {
    case '<':
      if(x<y) cond=1;
      break;
    case '>':
      if(x>y) cond=1;
      break;
    case '=':
      if(x==y) cond=1;
      break;
  }
  if(!cond) { /* throw away until ENDIF */
    int blockScope = 1 ;
    while (blockScope > 0) {
      if (tok == ELSE || tok == ENDIF) {
        if (--blockScope == 0) {
          break ;
        }
      }
      else if (tok == IF) {
        ++blockScope ;
      }
      else if (tok == FINISHED) {
        printf("if-statement has no else or endif ") ;
        serror(3) ;
      }
      get_token();
    }
  }
}

/*********** loop stack ************/

/* Push function for the FOR/WHILE stack. */
void lpush(struct loop_stack i)
{
   if(++ltos>=LOOP_NEST)
    serror(10);

  lstack[ltos]=i;
}

struct loop_stack lpop()
{
  if(ltos < 0)
     serror(11);

  return(lstack[ltos--]);
}

/*********** for statement ************/

/* Execute a FOR loop. */
void exec_for()
{
  struct loop_stack i;
  int value;

  get_token(); /* read the control variable */
  if(!islower(*token)) {
    serror(4);
    return;
  }

  i.var=*token-'a'; /* save its index */

  get_token(); /* read the equals sign */
  if(*token != '=') {
    serror(3);
    return;
  }

  get_exp(&value); /* get initial value */

  variables[i.var]=value;

  get_token();
  if(tok!=TO) serror(9); /* read and discard the TO */

  get_exp(&i.target); /* get target value */

  /* if loop can execute at least once, push info on stack */
  if(value <= i.target) {
    i.beginLoc = prog;
    i.endLoc = 0;
    i.breakLoc = 0;
    lpush(i);
  }
  else  { /* otherwise, skip loop code altogether */
    exit_block("For statement", FOR, NEXT);
#ifdef LOOPELSE
    /* check for for-else here, and execute */
    get_token() ;
    if (tok != ELSE) {
      putback() ;
    }
#endif
  }
}

/************ next statement **************/

void next()
{
  struct loop_stack *ii = &lstack[ltos];

  if (ltos == -1 || ii->var == 0xff) {
    serror(8) ;
  }

  if (ii->endLoc == 0) {  /* allow for fast break-stmt */
    ii->endLoc = prog ; /* point to statement after for-else construct */
#ifdef LOOPELSE
    get_token() ;
    if (tok == ELSE) {
      exit_block("If statement", IF, ENDIF) ;
    }
    else {
      putback() ;
      ii->endLoc = prog ; /* keep breakLoc and endLoc consistent */
    }
#endif
    ii->breakLoc = prog ; /* point to statement after for-else construct */
  }

  ++variables[ii->var]; /* increment control variable */
  if(variables[ii->var] <= ii->target) {
    prog = ii->beginLoc;  /* loop */
  }
  else {
    lpop() ;

#ifdef LOOPELSE
    /* check for for-else here, and execute if available */
    get_token() ;
    if (tok != ELSE) {
      putback() ;
    }
#endif
  }
}

/************ break statement **************/

void exec_break()
{
  if (lstack[ltos].breakLoc) {
    prog = lstack[ltos].breakLoc ; /* points past loop-else construct */
  }
  else {
    const char *msg;
    int bTok, eTok;

    if (lstack[ltos].var == 0xff) { /* while statement */
      msg = "While statement" ;
      bTok = WHILE ;
      eTok = WEND ;
    }
    else { /* for statement */
      msg = "For statement" ;
      bTok = FOR ;
      eTok = NEXT ;
    }

    exit_block(msg, bTok, eTok) ;

#ifdef LOOPELSE
    /* check for for-else here, and skip it due to break-statement exit */
    get_token() ;
    if (tok != ELSE) {
      putback() ;
    }
    else {
      exit_block("For-else block", IF, ENDIF) ;
    }
#endif
  }

  lpop() ;
}

/************ continue statement **************/

void exec_continue()
{
  struct loop_stack *ii = &lstack[ltos] ;

  if (ii->var == 0xff) { /* while statement */
    prog = ii->beginLoc ;
  }
  else { /* for statement */
    ++variables[ii->var]; /* increment control variable */
    if(variables[ii->var] <= ii->target) {
      prog = ii->beginLoc;  /* loop */
    }
    else {
      if (ii->endLoc) {
        prog = ii->endLoc ;
      }
      else {
        exit_block("For statement", FOR, NEXT) ; /* find next-stmt location */
      }

#ifdef LOOPELSE
      if (ii->endLoc != ii->breakLoc) { /* An else clause exists */
        /* Should/can endLoc point past the else? */
        get_token() ; /* skip past else keyword */
      }
#endif

      lpop() ; /* Now, we need to throw away the for loop context */
    }
  }
}

/************* while **********/

/* Execute an IF statement. */
void exec_while()
{
  struct loop_stack i ;
  int pushWhile = 0 ;
  int x , y;
  int cond;
  char op;

  if (ltos != -1) {
    if (lstack[ltos].beginLoc == lastTokPos) {
       /* This while statement is on TOS and active! Keep going! */
    }
    else {
      /* Do not allow direct While-stmt recursion. */
      /* Alternating between while and next statements, */
      /* or nesting more than one unique while statements is allowed */

      /* See if this while has been registered */
      /* at a different nest level. */
      for (int jj=ltos ; jj >= 0; --jj) {
        if (lstack[jj].var != 0xff) { /* no danger of direct recursion */
          break ;
        }
        if (lstack[jj].beginLoc == lastTokPos) {
          printf("while statement cannot be directly recursive ") ;
          serror(3);
        }
      }
      /* First encounter.  Create new while-statement nest */
      pushWhile = 1 ;
    }
  } 
  else {
    pushWhile = 1 ;
  }

  if (pushWhile) {
    i.beginLoc = lastTokPos ;
    i.endLoc = 0 ;
    i.breakLoc = 0 ;
    i.var = 0xff ; /* hack a nonsense var to indicate while-stmt */
  }

  get_exp(&x); /* get left expression */

  get_token(); /* get the operator */
  if(!strchr("=<>", *token)) {
    serror(0); /* not a legal operator */
    return;
  }
  op=*token;

  get_exp(&y); /* get right expression */

  /* determine the outcome */
  cond = 0;
  switch(op) {
    case '<':
      if(x<y) cond=1;
      break;
    case '>':
      if(x>y) cond=1;
      break;
    case '=':
      if(x==y) cond=1;
      break;
  }

  if(!cond) { /* is false so chew everything through wend */
    if (pushWhile == 0) { /* This while is on the stack top */
      if (lstack[ltos].endLoc) {  /* go to the else */
        prog = lstack[ltos].endLoc ;
      }
      else {
        exit_block("While loop", WHILE, WEND) ;
      }

#ifdef LOOPELSE
      if (lstack[ltos].endLoc != lstack[ltos].breakLoc) { /* else exists */
        get_token() ; /* skip else keyword */
      }
#endif
      lpop();
    }
    else {
      exit_block("While loop", WHILE, WEND) ;
#ifdef LOOPELSE
      get_token() ;
      if (tok != ELSE) {
        putback() ;
      }
#endif
    }
  }
  else if (pushWhile) {
    lpush(i) ;
  }
}

/************* wend **********/

void exec_wend()
{
  struct loop_stack *ii = &lstack[ltos] ;
  if (ltos == -1 || ii->var != 0xff) { /* check for while stmt */
    printf("wend found outside of while statement nest ") ;
    serror(3) ;
  }

  if (ii->endLoc == 0) {  /* allow for fast break-stmt */
    ii->endLoc = prog ; /* point to statement after for-else construct */
#ifdef LOOPELSE
    get_token() ;
    if (tok == ELSE) {
      exit_block("If statement", IF, ENDIF) ;
    }
    else {
      putback() ;
      ii->endLoc = prog ; /* keep breakLoc and endLoc consistent */
    }
#endif
    ii->breakLoc = prog ; /* point to statement after for-else construct */
  }

  prog = ii->beginLoc ;
}


/********* input statement *************/

/* Execute a simple form of the BASIC INPUT command */
void input()
{
  char var;
  int i;

  get_token(); /* see if prompt string is present */
  if(token_type==QUOTE) {
    printf(token); /* if so, print it and check for comma */
    get_token();
    if(*token!=',') serror(1);
    get_token();
  }
  else
     printf("? "); /* otherwise, prompt with / */

  var = *token-'a'; /* get the input var */

  scanf("%d", &i); /* read input */

  variables[var] = i; /* store it */
}

/********* gosub statement ************/

/* GOSUB stack push function. */
void gpush(char *s)
{
  if(++gtos == SUB_NEST) {
    serror(12);
    return;
  }

  gstack[gtos] = s;

}

/* Execute a computed GOSUB command. */
void gosub()
{
  char *loc;
  int value;

  get_exp(&value);
  /* find the label to call */
  loc = find_label(value);
  if(loc == 0)
    serror(7); /* label not defined */
  else {
    gpush(prog); /* save place to return to */
    prog = loc;  /* start program running at that loc */
  }
}

/********* return statement *********/

/* GOSUB stack pop function. */
char *gpop()
{
  if(gtos==0) {
    serror(13);
    return 0;
  }

  return(gstack[gtos--]);
}

/* Return from GOSUB. */
void greturn()
{
   prog = gpop();
}

/***************************************/
/************ Tiny Basic ***************/
/***************************************/

int main(int argc, char *argv[])
{
  char *p_buf;

  if(argc!=2) {
    printf("usage: tinybasic <filename>\n");
    exit(1);
  }

  /* allocate memory for the program */
  if(!(p_buf=(char *) malloc(PROG_SIZE))) {
    printf("allocation failure");
    exit(1);
  }

  /* load the program to execute */
  if(!load_program(p_buf,argv[1])) exit(1);

  if(setjmp(e_buf)) exit(1); /* initialize the long jump buffer */

  prog = p_buf;
  scan_labels(); /* find the labels in the program */
  ltos = -1; /* initialize the FOR stack index */
  gtos = 0;  /* initialize the GOSUB stack index */
  do {
    token_type = get_token();
    /* check for assignment statement */
    if(token_type==VARIABLE) {
      assignment(); /* must be assignment statement */
    }
    else /* is command */
      switch(tok) {
        case NEXT:
           next();
           break;
        case IF:
           exec_if();
           break;
        case ENDIF:
           break;
        case FOR:
           exec_for();
           break;
        case ELSE:
           exit_block("if-statement", IF, ENDIF) ;
           break;
        case WHILE:
           exec_while();
           break;
        case WEND:
           exec_wend();
           break;
        case BREAK:
           exec_break();
           break;
        case CONTINUE:
           exec_continue();
           break;
        case PRINT:
           print();
           break;
        case GOTO:
           exec_goto();
           break;
        case GOSUB:
           gosub();
           break;
        case RETURN:
           greturn();
           break;
        case INPUT:
           input();
           break;
        case END:
           exit(0);
      }
  } while (tok != FINISHED);
}
