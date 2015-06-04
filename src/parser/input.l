  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.1.50 */
/***************************************************************  -*-C-*-  ***/
%{
/**CFile***********************************************************************

  FileName    [input.l]

  PackageName [parser]

  Synopsis    [Lexical analyzer for the NuSMV input language]

  SeeAlso     [grammar.y]

  Author      [Marco Roveri]

  Copyright   [
  This file is part of the ``parser'' package of NuSMV version 2.
  Copyright (C) 1998-2005 by CMU and FBK-irst.

  NuSMV version 2 is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2 of the License, or (at your option) any later version.

  NuSMV version 2 is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuSMV see <http://nusmv.fbk.eu>
  or email to <nusmv-users@fbk.eu>.
  Please report bugs to <nusmv-users@fbk.eu>.

  To contact the NuSMV development board, email to <nusmv@fbk.eu>. ]

******************************************************************************/

#if HAVE_CONFIG_H
#include "nusmv-config.h"
#endif

#include "util.h"

#include "utils/utils.h"
#include "utils/ustring.h"
#include "node/node.h"
#include "utils/error.h"
#include "utils/WordNumber.h"

#include <ctype.h>
#include <stdlib.h> /* for strtol */
#include <limits.h> /* for LLONG_MAX */

#include "utils/portability.h" /* for errno */
#include "parser/grammar.h" /* For yacc/lex interaction */

/* For direct interpretation of atomic (ATOM and NUMBER)
   and boolan (TRUE and FALSE) constants. */
#include "parser/symbols.h"

static char rcsid[] UTIL_UNUSED = "$Id: input.l,v 1.12.2.4.4.30.4.18 2010-02-02 10:09:34 nusmv Exp $";

static int nusmv_skip_comment ARGS((void));

EXTERN void Parser_switch_to_psl ARGS((void));

/* The below code is only meaningful for flex version 2.5.31 which is
   buggy since it does not define the yy_prev_more_offset static
   variable */
#if defined YY_FLEX_SUBMINOR_VERSION &&         \
  defined YY_FLEX_MAJOR_VERSION &&              \
  defined YY_FLEX_MINOR_VERSION
#if YY_FLEX_SUBMINOR_VERSION == 31 &&           \
  YY_FLEX_MINOR_VERSION == 5 &&                 \
  YY_FLEX_MAJOR_VERSION == 2
static int yy_prev_more_offset = 0;
#endif
#endif

#if ! NUSMV_HAVE_ISATTY
static inline int isatty(int d) { return 0; }
#endif

/*
   The following are needed in order to allow parsing of long
   comments, that otherwise will cause errors since flex thinks that
   it is using REJECT even if it isn't.  The "%option noreject" seems
   to be ignored in the latest (and previous) versions of flex.
*/
#ifdef YY_USES_REJECT
#undef YY_USES_REJECT
#endif

#if NUSMV_HAVE_ERRNO_H
#define YY_INPUT(buf, result, max_size) \
        if ( YY_CURRENT_BUFFER->yy_is_interactive ) \
                { \
                int c = '*', n; \
                for (n=0; n<max_size && \
                     (c = getc(yyin)) != EOF && \
                     c!=' ' && c!='\n' && c!='\t' && c!='\r' && c!='\f'; ++n ) \
                        buf[n] = (char) c; \
                if (c==' ' || c=='\n' || c=='\t' || c=='\r' || c=='\f') buf[n++] = (char) c; \
                if (c == EOF && ferror(yyin)) YY_FATAL_ERROR( "input in flex scanner failed" ); \
                result = n; \
                } \
        else \
                { \
                errno=0; \
                while ( (result = fread(buf, 1, max_size, yyin))==0 && ferror(yyin)) \
                        { \
                        if(errno != EINTR) \
                                { \
                                YY_FATAL_ERROR( "input in flex scanner failed" ); \
                                break; \
                                } \
                        errno=0; \
                        clearerr(yyin); \
                        } \
                }
#else /*  NUSMV_HAVE_ERRNO_H */
#define YY_INPUT(buf, result, max_size) \
        if ( YY_CURRENT_BUFFER->yy_is_interactive ) \
                { \
                int c = '*', n; \
                for (n=0; n<max_size && \
                     (c = getc(yyin)) != EOF && \
                     c!=' ' && c!='\n' && c!='\t' && c!='\r' && c!='\f'; ++n ) \
                        buf[n] = (char) c; \
                if (c==' ' || c=='\n' || c=='\t' || c=='\r' || c=='\f') buf[n++] = (char) c; \
                if (c == EOF && ferror(yyin)) YY_FATAL_ERROR( "input in flex scanner failed" ); \
                result = n; \
                } \
        else \
                { \
                while ( (result = fread(buf, 1, max_size, yyin))==0 && ferror(yyin)) \
                        { \
                        clearerr(yyin); \
                        } \
                }
#endif /* NUSMV_HAVE_ERRNO_H */

%}
%a        15000
%o        25000

%pointer
%option yylineno
%option noreject
%option always-interactive
  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.1.50 */
%%
  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.25 */
  /* **************************************************************  -*-C-*-  ***/

[ \n\t\r\f]             ;
"--"                    nusmv_skip_comment();
^"#"" "[0-9]+.*\n       sscanf(yytext,"# %d",&yylineno);
^"#".*\n                rpterr("Unexpected preprocessor directive:\n %s\n",yytext);
  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.25 */
  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.50 */
  /* **************************************************************  -*-C-*-  ***/

"MODULE"                {yylval.lineno = yylineno; return(TOK_MODULE);}
"process"               {yylval.lineno = yylineno; return(TOK_PROCESS);}
"DEFINE"                {yylval.lineno = yylineno; return(TOK_DEFINE);}
"MDEFINE"               {yylval.lineno = yylineno; return(TOK_ARRAY_DEFINE);}
"VAR"                   {yylval.lineno = yylineno; return(TOK_VAR);}
"FROZENVAR"             {yylval.lineno = yylineno; return(TOK_FROZENVAR);}
"IVAR"                  {yylval.lineno = yylineno; return(TOK_IVAR);}
"INIT"                  {yylval.lineno = yylineno; return(TOK_INIT);}
"TRANS"                 {yylval.lineno = yylineno; return(TOK_TRANS);}
"INVAR"                 {yylval.lineno = yylineno; return(TOK_INVAR);}
"SPEC"                  {yylval.lineno = yylineno; return(TOK_SPEC);}
"CTLSPEC"               {yylval.lineno = yylineno; return(TOK_CTLSPEC);}
"LTLSPEC"               {yylval.lineno = yylineno; return(TOK_LTLSPEC);}
"PSLSPEC"               {yylval.lineno = yylineno; Parser_switch_to_psl(); return(TOK_PSLSPEC);}
"COMPUTE"               {yylval.lineno = yylineno; return(TOK_COMPUTE);}
"INVARSPEC"             {yylval.lineno = yylineno; return(TOK_INVARSPEC);}
"NAME"                  {yylval.lineno = yylineno; return(TOK_NAME);}
"CONSTRAINT"            {yylval.lineno = yylineno; return(TOK_CONSTRAINT);}
"CONSTANTS"             {yylval.lineno = yylineno; return(TOK_CONSTANTS);}
"SIMPWFF"               {yylval.lineno = yylineno; return(TOK_SIMPWFF);}
"NEXTWFF"               {yylval.lineno = yylineno; return(TOK_NEXTWFF);}
"CTLWFF"                {yylval.lineno = yylineno; return(TOK_CTLWFF);}
"LTLWFF"                {yylval.lineno = yylineno; return(TOK_LTLWFF);}
"COMPWFF"               {yylval.lineno = yylineno; return(TOK_COMPWFF);}
"COMPID"                {yylval.lineno = yylineno; return(TOK_COMPID);}
"IN"                    {yylval.lineno = yylineno; return(TOK_INCONTEXT);}
"FAIRNESS"              {yylval.lineno = yylineno; return(TOK_FAIRNESS);}
"JUSTICE"               {yylval.lineno = yylineno; return(TOK_JUSTICE);}
"COMPASSION"            {yylval.lineno = yylineno; return(TOK_COMPASSION);}
"ISA"                   {yylval.lineno = yylineno; return(TOK_ISA);}
"ASSIGN"                {yylval.lineno = yylineno; return(TOK_ASSIGN);}

"array"                 {yylval.lineno = yylineno; return(TOK_ARRAY);}
"bool"                  {yylval.lineno = yylineno; return(TOK_BOOL);}
"of"                    {yylval.lineno = yylineno; return(TOK_OF);}
"boolean"               {yylval.lineno = yylineno; return(TOK_BOOLEAN);}
"integer"               {yylval.lineno = yylineno; return(TOK_INTEGER);}
"Integer"               {yylval.lineno = yylineno; return(TOK_INTEGER);}
"real"                  {yylval.lineno = yylineno; return(TOK_REAL);}
"Real"                  {yylval.lineno = yylineno; return(TOK_REAL);}
"word1"                 {yylval.lineno = yylineno; return(TOK_WORD1);}
"word"                  {yylval.lineno = yylineno; return(TOK_WORD);}
"Word"                  {yylval.lineno = yylineno; return(TOK_WORD);}

"signed"                {yylval.lineno = yylineno; return(TOK_SIGNED);}
"unsigned"              {yylval.lineno = yylineno; return(TOK_UNSIGNED);}
"extend"                {yylval.lineno = yylineno; return(TOK_EXTEND);}

"uwconst"               {yylval.lineno = yylineno; return(TOK_UWCONST);}
"swconst"               {yylval.lineno = yylineno; return(TOK_SWCONST);}

"resize"                {yylval.lineno = yylineno; return(TOK_WRESIZE);}
"sizeof"                {yylval.lineno = yylineno; return(TOK_WSIZEOF);}
"toint"                 {yylval.lineno = yylineno; return(TOK_WTOINT);}
"count"                 {yylval.lineno = yylineno; return(TOK_COUNT);}

"READ"                  {yylval.lineno = yylineno; return(TOK_WAREAD);}
"WRITE"                 {yylval.lineno = yylineno; return(TOK_WAWRITE);}

"EX"                    {yylval.lineno = yylineno; return(TOK_EX);}
"AX"                    {yylval.lineno = yylineno; return(TOK_AX);}
"EF"                    {yylval.lineno = yylineno; return(TOK_EF);}
"AF"                    {yylval.lineno = yylineno; return(TOK_AF);}
"EG"                    {yylval.lineno = yylineno; return(TOK_EG);}
"AG"                    {yylval.lineno = yylineno; return(TOK_AG);}
"E"                     {yylval.lineno = yylineno; return(TOK_EE);}
"F"                     {yylval.lineno = yylineno; return(TOK_OP_FUTURE);}
"O"                     {yylval.lineno = yylineno; return(TOK_OP_ONCE);}
"G"                     {yylval.lineno = yylineno; return(TOK_OP_GLOBAL);}
"H"                     {yylval.lineno = yylineno; return(TOK_OP_HISTORICAL);}
"X"                     {yylval.lineno = yylineno; return(TOK_OP_NEXT);}
"Y"                     {yylval.lineno = yylineno; return(TOK_OP_PREC);}
"Z"                     {yylval.lineno = yylineno; return(TOK_OP_NOTPRECNOT);}
"A"                     {yylval.lineno = yylineno; return(TOK_AA);}
"U"                     {yylval.lineno = yylineno; return(TOK_UNTIL);}
"S"                     {yylval.lineno = yylineno; return(TOK_SINCE);}
"V"                     {yylval.lineno = yylineno; return(TOK_RELEASES);}
"T"                     {yylval.lineno = yylineno; return(TOK_TRIGGERED);}
"BU"                    {yylval.lineno = yylineno; return(TOK_BUNTIL);}
"EBF"                   {yylval.lineno = yylineno; return(TOK_EBF);}
"ABF"                   {yylval.lineno = yylineno; return(TOK_ABF);}
"EBG"                   {yylval.lineno = yylineno; return(TOK_EBG);}
"ABG"                   {yylval.lineno = yylineno; return(TOK_ABG);}
"MIN"                   {yylval.lineno = yylineno; return(TOK_MMIN);}
"MAX"                   {yylval.lineno = yylineno; return(TOK_MMAX);}
"("                     {yylval.lineno = yylineno; return(TOK_LP);}
")"                     {yylval.lineno = yylineno; return(TOK_RP);}
"["                     {yylval.lineno = yylineno; return(TOK_LB);}
"]"                     {yylval.lineno = yylineno; return(TOK_RB);}
"{"                     {yylval.lineno = yylineno; return(TOK_LCB);}
"}"                     {yylval.lineno = yylineno; return(TOK_RCB);}
"FALSE"                 {
                                yylval.node = new_node(FALSEEXP,Nil,Nil);
                                return(TOK_FALSEEXP);
                        }
"TRUE"                  {
                                yylval.node = new_node(TRUEEXP,Nil,Nil);
                                return(TOK_TRUEEXP);
                        }
"case"                  {yylval.lineno = yylineno; return(TOK_CASE);}
"esac"                  {yylval.lineno = yylineno; return(TOK_ESAC);}
":="                    {yylval.lineno = yylineno; return(TOK_EQDEF);}
"+"                     {yylval.lineno = yylineno; return(TOK_PLUS);}
"-"                     {yylval.lineno = yylineno; return(TOK_MINUS);}
"*"                     {yylval.lineno = yylineno; return(TOK_TIMES);}
"/"                     {yylval.lineno = yylineno; return(TOK_DIVIDE);}
"mod"                   {yylval.lineno = yylineno; return(TOK_MOD);}
"<<"                    {yylval.lineno = yylineno; return(TOK_LSHIFT);}
">>"                    {yylval.lineno = yylineno; return(TOK_RSHIFT);}
"<<<"                   {yylval.lineno = yylineno; return(TOK_LROTATE);}
">>>"                   {yylval.lineno = yylineno; return(TOK_RROTATE);}
"="                     {yylval.lineno = yylineno; return(TOK_EQUAL);}
"!="                    {yylval.lineno = yylineno; return(TOK_NOTEQUAL);}
"<="                    {yylval.lineno = yylineno; return(TOK_LE);}
">="                    {yylval.lineno = yylineno; return(TOK_GE);}
"<"                     {yylval.lineno = yylineno; return(TOK_LT);}
">"                     {yylval.lineno = yylineno; return(TOK_GT);}
"next"                  {yylval.lineno = yylineno; return(TOK_NEXT);}
"init"                  {yylval.lineno = yylineno; return(TOK_SMALLINIT);}
"self"                  {yylval.lineno = yylineno; return(TOK_SELF);}
"union"                 {yylval.lineno = yylineno; return(TOK_UNION);}
"in"                    {yylval.lineno = yylineno; return(TOK_SETIN);}
".."                    {yylval.lineno = yylineno; return(TOK_TWODOTS);}
"."                     {yylval.lineno = yylineno; return(TOK_DOT);}
"->"                    {yylval.lineno = yylineno; return(TOK_IMPLIES);}
"<->"                   {yylval.lineno = yylineno; return(TOK_IFF);}
"|"                     {yylval.lineno = yylineno; return(TOK_OR);}
"&"                     {yylval.lineno = yylineno; return(TOK_AND);}
"xor"                   {yylval.lineno = yylineno; return(TOK_XOR);}
"xnor"                  {yylval.lineno = yylineno; return(TOK_XNOR);}
"!"                     {yylval.lineno = yylineno; return(TOK_NOT);}
"?"                     {yylval.lineno = yylineno; return(TOK_QUESTIONMARK);}
","                     {yylval.lineno = yylineno; return(TOK_COMMA);}
":"                     {yylval.lineno = yylineno; return(TOK_COLON);}
";"                     {yylval.lineno = yylineno; return(TOK_SEMI);}
"::"                    {yylval.lineno = yylineno; return(TOK_CONCATENATION);}


"PRED"                  {yylval.lineno = yylineno; return(TOK_PRED);}
"PREDICATES"            {yylval.lineno = yylineno; return(TOK_PREDSLIST);}
"MIRROR"                {yylval.lineno = yylineno; return(TOK_MIRROR);}
  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.50 */
  /* BEGINS: input.l.2.55 */
  /* **************************************************************  -*-C-*-  ***/

"GAME"                  {yylval.lineno = yylineno; return(TOK_GAME);}
"PLAYER_1"              {yylval.lineno = yylineno; return(TOK_PLAYER_1);}
"PLAYER_2"              {yylval.lineno = yylineno; return(TOK_PLAYER_2);}
"REACHTARGET"           {yylval.lineno = yylineno; return(TOK_REACHTARGET);}
"AVOIDTARGET"           {yylval.lineno = yylineno; return(TOK_AVOIDTARGET);}
"REACHDEADLOCK"         {yylval.lineno = yylineno; return(TOK_REACHDEADLOCK);}
"AVOIDDEADLOCK"         {yylval.lineno = yylineno; return(TOK_AVOIDDEADLOCK);}
"BUCHIGAME"             {yylval.lineno = yylineno; return(TOK_BUCHIGAME);}
"LTLGAME"               {yylval.lineno = yylineno; return(TOK_LTLGAME);}
"GENREACTIVITY"         {yylval.lineno = yylineno; return(TOK_GENREACTIVITY);}
  /* ENDS: input.l.2.55 */
  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.75 */
  /* **************************************************************  -*-C-*-  ***/

 /* word constants */
"0"([us])?[bBoOdDhH][0-9]*"_"[0-9a-fA-F][0-9a-fA-F_]* {
                 char* errorString;
                 WordNumber_ptr wordConstant
                        = WordNumber_from_parsed_string(yytext, &errorString);
                 /* check for errors */
                 if (WORD_NUMBER(NULL) == wordConstant) rpterr("%s", errorString);
                 yylval.node = new_node('s' == yytext[1]
                                        ? NUMBER_SIGNED_WORD : NUMBER_UNSIGNED_WORD,
                                        (node_ptr)wordConstant,Nil);
                 return(TOK_NUMBER_WORD);
               }

 /* real, fractional and exponential constants */
[fF]"'"[0-9]+"/"[0-9]+  {
                  yytext[0] = 'f';
                  yylval.node = new_node(NUMBER_FRAC,
                                         (node_ptr)find_string(yytext),Nil);
                  return(TOK_NUMBER_FRAC);
                 }

[0-9]+("."[0-9]+)?[eE][+-]?[0-9]+ {
                  yylval.node = new_node(NUMBER_EXP,
                                         (node_ptr)find_string(yytext),Nil);
                  return(TOK_NUMBER_EXP);
                 }

[0-9]+"."[0-9]+  {
                  yylval.node = new_node(NUMBER_REAL,
                                         (node_ptr)find_string(yytext),Nil);
                  return(TOK_NUMBER_REAL);
                 }

 /* integer number */
[0-9]+           {
                  long tmp;
                  char* endptr;

                  errno = 0;
                  tmp = strtol(yytext, &endptr, 10);

                  /* range errors */
                  if ((errno == ERANGE && (tmp == LONG_MAX || tmp == LONG_MIN))
                      || (errno != 0 && tmp == 0)

                      /* no digits found */
                      || (endptr == yytext)

                      /* garbage after digits */
                      || (*endptr != '\0')

                      /* as an additional check, verify that the value can
                         fit into an ordinary int. tmp can not be negative */
                      || (tmp < 0) || (INT_MAX < tmp)) {

                    rpterr("illegal integer: \"%s\"", yytext);
                  }

                  /* here tmp can be safely cast to int */
                  yylval.node = new_node(NUMBER, NODE_FROM_INT((int)(tmp)), Nil);
                  return(TOK_NUMBER);
                 }

 /* identifier */
[A-Za-z_][A-Za-z0-9_\$#-]*  {
                  yylval.node = new_node(ATOM,
                                         (node_ptr)find_string(yytext),Nil);
                  return(TOK_ATOM);
                 }
\"[^\"]*\"       {
                  yylval.node = new_node(ATOM,(node_ptr)find_string(yytext),Nil);
                  return(TOK_ATOM);
                 } /* Unused token */

.                 rpterr("illegal character : \"%s\"", yytext);
  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.2.75 */
%%
  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.3.50 */
/***************************************************************  -*-C-*-  ***/
static int nusmv_skip_comment()
{
  register int c;

  do {
    c = input();
  } while ( c != '\n' && c != EOF );
  return(0);
}

  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/input.l.3.50 */
