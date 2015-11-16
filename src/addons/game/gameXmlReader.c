/**CFile***********************************************************************

  FileName    [ gameXmlReader.c ]

  PackageName [ game ]

  Synopsis    [ The file contains functions to read an XML file generated
                with the RAT tool. ]

  Description [ This file is compiled only if the Expat XML library
                was available during configuration. ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game'' package of NuGaT.
  Copyright (C) 2010 by FBK-irst.

  NuGaT is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  NuGaT is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuGaT see <http://es.fbk.eu/tools/nugat>
  or email to <nugat-users@list.fbk.eu>.
  Please report bugs to <nugat-users@list.fbk.eu>.

  To contact the NuGaT development board, email to <nugat@list.fbk.eu>. ]

******************************************************************************/

#if HAVE_CONFIG_H
# include "config.h"
#endif

#if HAVE_LIBEXPAT

#include "game.h"
#include "gameInt.h"
#include "GamePlayer.h"
#include "parser/game_symbols.h"

#include "compile/compile.h"
#include "node/node.h"
#include "opt/opt.h"
#include "parser/parser.h"
#include "parser/symbols.h"
#include "utils/utils.h"
#include "utils/error.h"
#include "nusmv/core/utils/ErrorMgr.h"

#include <ctype.h> /* for isspace */
#include <expat.h>
#include <stdio.h>
#include <string.h>

static char rcsid[] UTIL_UNUSED = "$Id: gameXmlReader.c,v 1.1.2.9 2010-02-09 21:01:54 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Structure******************************************************************

  Synopsis    [ This is a structure which keeps all the elements during
                the parsing of an XML file. ]

  Description [ This structure was defined in such a way that it is
                easy to convert it to a parse tree returned by the
                NuGaT parser. ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct XmlParseResult_TAG
{
  /* Fields to store the final result. */

  node_ptr input_vars;  /* A list (connected by CONS) of pairs
                           (connected by COLON) of an input var name
                           and its type (represented as in the NuGaT
                           parser). */
  node_ptr output_vars; /* Similar to input_vars, but a list of output
                           vars and their types. */
  node_ptr assumptions; /* A tree (connected by AND) of PSL
                           expressions representing the assumptions on
                           the input behavior. */
  node_ptr guarantees;  /* A tree (connected by AND) of PSL
                           expressions representing the guarantees on
                           the output behavior. */

  /* Fields to store intermediate results. */

  XML_Parser parser; /* The XML parser used. */
  boolean isIgnore;  /* A flag that all elements are ignored till the
                        end tag of an element on the stack. */
  node_ptr stack;    /* A list (stack) of parsed elements. every new
                        element is added at the top (beginning). When
                        a tag is met a node with this tag is added to
                        the beginning of the stack. When end-tag is
                        met, all internals are processed, removed and
                        a composed structure is added as left child of
                        the tag node. */
} XmlParseResult;
typedef struct XmlParseResult_TAG* XmlParseResult_ptr;

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Enum***********************************************************************

  Synopsis    [ A list of all possible XML elements that could occur. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
enum XmlTags {
  XML_ERROR = -1,

  XML_PROJECT,

  XML_PROPERTY_SYNTHESIS,
  XML_PROPERTY_SIMULATION,
  XML_PROPERTY_ASSURANCE,

  XML_SIGNALS,
  XML_REQUIREMENTS, /* 5 */
  XML_POSSIBILITIES,
  XML_ASSERTIONS,

  XML_SIGNAL,

  XML_KIND,
  XML_TOGGLED,

  XML_POSSIBILITY, /* 10 */
  XML_ASSERTION,
  XML_REQUIREMENT,

  XML_NAME,
  XML_PROPERTY,
  XML_STATUS, /* 15 */
  XML_NOTES,
  XML_TYPE,
  XML_EDITABLE,
  XML_ACTIVE_VIEW,

  XML_CATEGORIES, /* 20 */
  XML_CATEGORY,
  XML_TRACE,

  XML_DEPENDENCIES,
  XML_DEPENDENCY,

  XML_LOOPS,

  XML_CREATION_INFO,

  XML_STRIPE,
  XML_STEP,
  XML_VALUE,

  /* 30 */
  XML_TEXT, /* Artificial tag to store text on the stack. left is
               char* text. right is a flag: 0 - end tag is not met, 1
               - end tag is met. */

  XML_BASE_AUTOMATON_NAME,
  XML_AUTOMATON_PARAMETER,
  XML_AUTOMATA,
  XML_AUTO_SIGNAL
};

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN cmp_struct_ptr cmps;

EXTERN FILE* nusmv_stderr;


EXTERN node_ptr parsed_tree;

EXTERN int yylineno;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ The size of a buffer used during reading XML files. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
#define BUFFSIZE 8192

/**Macro***********************************************************************

  Synopsis    [ The size of a buffer used during reading ids in XML files. ]

  Description [ This is the actual size of the char array. To allow
                for trailing '0' and checking for overflow the actual
                maximum length of identifiers is 2 less.

                Hence, the minimum allowed value is 3.

                The decimal representation of IDBUFSIZE - 1 must take
                up less than 10 characters, i.e., the maximal allowed
                value is 1000000000. ]

  SeeAlso     [ ]

******************************************************************************/
#define IDBUFSIZE 1000

/**Macro***********************************************************************

  Synopsis    [ To cast instances of XmlParseResult. ]

  Description [ These macros must be used respectively to cast and to
                check instances of XmlParseResult. ]

  SideEffects [ None ]

  SeeAlso     [ ]

******************************************************************************/
#define XML_PARSE_RESULT(x) ((XmlParseResult_ptr) x)

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void game_xml_reader_tag_begin ARGS((NuSMVEnv_ptr env,
                                            void* data,
                                            const char* name,
                                            const char** atts));

static void game_xml_reader_tag_end ARGS((NuSMVEnv_ptr env,
                                          void* data,
                                          const char *string));

static void game_xml_reader_char_handler ARGS((NuSMVEnv_ptr env,
                                               void* data,
                                               const char *txt,
                                               int len));

static node_ptr game_xml_reader_pop_stack ARGS((NodeMgr_ptr nodemgr,node_ptr* stack));

static node_ptr game_xml_reader_pop_stack_cleanly ARGS((NodeMgr_ptr nodemgr,node_ptr* stack));

static void game_xml_reader_free_text_node ARGS((NodeMgr_ptr nodemgr, node_ptr text_node));

static node_ptr game_xml_reader_parse_type ARGS((NuSMVEnv_ptr env,const char* text));

static enum XmlTags game_xml_reader_identify_tag ARGS((const char* txt));

static XmlParseResult_ptr
gameXmlReader_XmlParseResult_create ARGS((const ErrorMgr_ptr errmgr,XML_Parser parser));

static void
gameXmlReader_XmlParseResult_destroy_parser ARGS((XmlParseResult_ptr self));

static void
gameXmlReader_XmlParseResult_destroy ARGS((XmlParseResult_ptr self));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Takes a filename, opens the file and parses it. ]

  Description [ Returns 0 if successful and 1 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int Game_RatFileToGame(NuSMVEnv_ptr env,const char *filename)
{
  XmlParseResult_ptr parseResult;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings =  USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  if (cmp_struct_get_read_model(cmps)) {
    fprintf(nusmv_stderr,
            "A model appears to be already read from file: %s.\n",
            get_input_file(OptsHandler_create()));
    return(1);
  }

  /* Open the file, create the parser, and parse the file. */
  {
    FILE* file;
    int done = 0;
    int len;
    char inBuffer[BUFFSIZE]; /* a buffer used by the parser */
    XML_Parser parser;

    /* Open the file. */
    file = fopen(filename, "r");
    if (file == (FILE*) NULL) ErrorMgr_rpterr(errmgr,"cannot open input XML file %s", filename);
    yylineno = 1;

    /* Create parser and parseResult. */
    parser = XML_ParserCreate(NULL);
    if (!parser) ErrorMgr_error_out_of_memory(errmgr,0);
    parseResult = gameXmlReader_XmlParseResult_create(errmgr,parser);

    XML_SetUserData(parser, parseResult);
    XML_SetElementHandler(parser,
                          &game_xml_reader_tag_begin,
                          &game_xml_reader_tag_end);
    XML_SetCharacterDataHandler(parser,
                                &game_xml_reader_char_handler);

    /* Parse the file. */
    CATCH(errmgr) {
      while (!done) {
        len = fread(inBuffer, sizeof(char), BUFFSIZE, file);

        if (ferror(file)) {
          ErrorMgr_rpterr(errmgr,"IO Error in reading XML file");
        }

        done = feof(file);

        if (!XML_Parse(parser, inBuffer, len, done)) {
          ErrorMgr_rpterr(errmgr,"Parse error (XML file) at line %d:\n%s\n",
                 XML_GetCurrentLineNumber(parser),
                 XML_ErrorString(XML_GetErrorCode(parser)));
        }
      } /* while */
    }
    FAIL(errmgr) {
      fclose(file);
      gameXmlReader_XmlParseResult_destroy(parseResult);
      ErrorMgr_rpterr(errmgr,"Parser error");
    };

    /* Clean up and check. From now on only the data read into
       parseResult is needed. */

    fclose(file);
    gameXmlReader_XmlParseResult_destroy_parser(parseResult);

    if (Nil != game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack)) {
      gameXmlReader_XmlParseResult_destroy(parseResult);
      ErrorMgr_rpterr(errmgr,"Parse error (XML file): stack is not empty after parsing.\n");
    }
  }

  /* Here we create a parse tree of a game structure from the read XML
     file. Player 1 is the input. Player 2 is the output. */
  {
    node_ptr init1, init2, trans1, trans2, property;
    node_ptr module1, module2;

    init1 = init2 = trans1 = trans2 = property = Nil;
    module1 = module2 = Nil;

//     /* debugging printing */
//   fprintf(nusmv_stderr, "\n--PARSED XML FILE:\n");
//   fprintf(nusmv_stderr, "\n--ASSUMPTION:\n--");
//   print_node(nusmv_stderr, parseResult->assumptions);
//   fprintf(nusmv_stderr, "\n\n--GUARANTEES:\n--");
//   print_node(nusmv_stderr, parseResult->guarantees);
//   fprintf(nusmv_stderr, "\n\n");

    /* Divide each of the assumptions and guarantees on 3 sets, i.e.,
       initial condition (no temporal operators), transitions relation
       (only next temporal operator), and remaining requirements.

       Transformations are applied to try and fit more
       assumptions/guarantees into the init or trans categories.
    */
    Game_PropertyToGame(env,
                        &parseResult->input_vars,
                        &parseResult->output_vars,
                        parseResult->assumptions,
                        &init1,
                        &trans1,
                        parseResult->guarantees,
                        &init2,
                        &trans2,
                        &property);

    if (Nil != parseResult->input_vars) {
      module1 = cons(nodemgr,new_node(nodemgr,VAR, parseResult->input_vars, Nil), module1);
    }
    if (Nil != init1) {
      module1 = cons(nodemgr,new_node(nodemgr,INIT, init1, Nil), module1);
    }
    if (Nil != trans1) {
      module1 = cons(nodemgr,new_node(nodemgr,TRANS, trans1, Nil), module1);
    }

    if (Nil != parseResult->output_vars) {
      module2 = cons(nodemgr,new_node(nodemgr,VAR, parseResult->output_vars, Nil), module2);
    }
    if (Nil != init2) {
      module2 = cons(nodemgr,new_node(nodemgr,INIT, init2, Nil), module2);
    }
    if (Nil != trans2) {
      module2 = cons(nodemgr,new_node(nodemgr,TRANS, trans2, Nil), module2);
    }

    /* Create the players\' MODULE (the same as NuGaT parser does). */
    module1 = new_node(nodemgr,MODULE,
                       new_node(nodemgr,MODTYPE,
                                new_node(nodemgr,ATOM,
                                         (node_ptr) UStringMgr_find_string(strings,PLAYER_NAME_1),
                                         Nil),
                                Nil),
                       module1);
    module2 = new_node(nodemgr,MODULE,
                       new_node(nodemgr,MODTYPE,
                                new_node(nodemgr,ATOM,
                                         (node_ptr) UStringMgr_find_string(strings,PLAYER_NAME_2),
                                         Nil),
                                Nil),
                       module2);

    /* Create a GAME structure as the NuGaT parser does it. */
    parsed_tree = new_node(nodemgr,GAME,
                           cons(nodemgr,property, Nil),
                           cons(nodemgr,module1,
                                cons(nodemgr,module2,
                                     Nil /*module list is empty*/)));

//     /* debugging printing */
//   fprintf(nusmv_stderr, "PARSED XML FILE:\nGAME\n\n");
//   fprintf(nusmv_stderr, "PLAYER_1\nVAR ");
//   print_sexp(nusmv_stderr, parseResult->input_vars);
//   fprintf(nusmv_stderr, "\nINIT :\n");
//   print_node(nusmv_stderr, init1);
//   fprintf(nusmv_stderr, "\nTRANS :\n");
//   print_node(nusmv_stderr, trans1);
//   fprintf(nusmv_stderr, "\n\nPLAYER_2\nVAR :\n");
//   print_sexp(nusmv_stderr, parseResult->output_vars);
//   fprintf(nusmv_stderr, "\nINIT:\n");
//   print_node(nusmv_stderr, init2);
//   fprintf(nusmv_stderr, "\nTRANS:\n");
//   print_node(nusmv_stderr, trans2);
//   fprintf(nusmv_stderr, "\nPROPERTY:\n");
//   print_node(nusmv_stderr, property);
//   fprintf(nusmv_stderr, "\n\n");
  }


  if (!opt_game_game(OptsHandler_create())) {
    Game_Mode_Enter(env);
  }
  cmp_struct_set_read_model(cmps);

  gameXmlReader_XmlParseResult_destroy(parseResult);

  return 0;
}

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Takes a stack and pops its head. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ game_xml_reader_pop_stack_cleanly ]

******************************************************************************/
static node_ptr game_xml_reader_pop_stack(NodeMgr_ptr nodemgr,node_ptr* stack) {
  node_ptr head;
  node_ptr element;

  head = *stack;

  if (Nil == head) return Nil;

  element = car(head);
  *stack = cdr(head);

  free_node(nodemgr,head);

  return element;
}

/**Function********************************************************************

  Synopsis    [ Takes a stack and pops its head. If the head is TEXT with
                zero (or white space) characters, it is removed and
                the procedure is repeated. ]

  Description [ The difference to game_xml_reader_pop_stack is that
                here the stack is cleaned from useless TEXT nodes,
                which are created after each element tag, and which
                has to be ignored. ]

  SideEffects [ ]

  SeeAlso     [ game_xml_reader_pop_stack ]

******************************************************************************/
static node_ptr game_xml_reader_pop_stack_cleanly(NodeMgr_ptr nodemgr,node_ptr* stack) {
  node_ptr head = game_xml_reader_pop_stack(nodemgr,stack);

  while (Nil != head
         && XML_TEXT == node_get_type(head)
         && '\0' == ((char*) car(head))[0]) {
    game_xml_reader_free_text_node(nodemgr,head);
    head = game_xml_reader_pop_stack(nodemgr,stack);
  }

  return head;
}

/**Function********************************************************************

  Synopsis    [ Takes an XML_TEXT node and frees the required memory,
                i.e., deallocates its left child and frees the node. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_xml_reader_free_text_node(NodeMgr_ptr nodemgr,node_ptr text_node) {
  node_ptr l;

  nusmv_assert(node_get_type(text_node) == XML_TEXT);

  l = car(text_node);

  FREE(l); /* FREE requires l-value */
  free_node(nodemgr,text_node);
}

/**Function********************************************************************

  Synopsis    [ Takes a string (char*), parses it, and returns a node_ptr
                the same way as NuGaT parser does it.]

  Description [ The kinds of types are very simplified, since RAT
                generates them. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_xml_reader_parse_type(NuSMVEnv_ptr env,const char* text) {
  int i1;
  int i2;
  int size = -1; /* size has some default, for sure wrong value */

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings =  USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  if (0 == strcmp(text, "boolean")) {
    return new_node(nodemgr,BOOLEAN, Nil, Nil);
  }
  else if (0 == strcmp(text, "integer")) {
    return new_node(nodemgr,INTEGER, Nil, Nil);
  }
  else if (0 == strcmp(text, "real")) {
    return new_node(nodemgr,REAL, Nil, Nil);
  }
  else if (1 == sscanf(text, "word [ %d ] %n", &i1, &size) ||
           1 == sscanf(text, "unsigned word [ %d ] %n", &i1, &size)) {
    if (-1 == size || text[size] != '\0') {
      ErrorMgr_rpterr(errmgr,"Incorrect XML file (word type)");
    }
    return new_node(nodemgr,UNSIGNED_WORD,
                    new_node(nodemgr,NUMBER,
                             NODE_FROM_INT(i1),
                             Nil),
                    Nil);
  }
  else if (1 == sscanf(text, "signed word [ %d ] %n", &i1, &size)) {
    if (-1 == size || text[size] != '\0') {
      ErrorMgr_rpterr(errmgr,"Incorrect XML file (word type)");
    }
    return new_node(nodemgr,SIGNED_WORD,
                    new_node(nodemgr,NUMBER,
                             NODE_FROM_INT(i1),
                             Nil),
                    Nil);
  }
  /* a range, i.e. int .. int */
  else if (1 == sscanf(text, "%d %n", &i1, &size)) {
    if (-1 == size) {
      ErrorMgr_rpterr(errmgr,"01 Incorrect XML file %%d .. %%d (range) type");
    }
    text += size;
    size = -1;
    sscanf(text, ".. %n", &size);
    if (-1 == size) {
      ErrorMgr_rpterr(errmgr,"02 Incorrect XML file %%d .. %%d (range) type");
    }
    text += size;
    size = -1;
    if (1 == sscanf(text, "%d %n", &i2, &size)) {
      if (-1 == size) ErrorMgr_rpterr(errmgr,"03 Incorrect XML file %%d .. %%d (range) type");
      return new_node(nodemgr,TWODOTS,
                      new_node(nodemgr,NUMBER, NODE_FROM_INT(i1), Nil),
                      new_node(nodemgr,NUMBER, NODE_FROM_INT(i2), Nil));
    }
    else {
      ErrorMgr_rpterr(errmgr,"04 Incorrect XML file %%d .. %%d (range) type");
    }
  }
  /* a list of values */
  else if (0 == strncmp(text, "{", 1)) {
    int size;
    node_ptr listOfVals = Nil;
    boolean end = false;

    sscanf(text, "{ %n", &size);
    text += size;

    while (!end) {
      int i;
      char buf[IDBUFSIZE]; /* IDBUFSIZE chars must be enough to hold
                              any identifier. */
      node_ptr newNode;

      if (1 == sscanf(text, "%d %n", &i, &size)) {
        text += size;
        newNode = new_node(nodemgr,NUMBER, NODE_FROM_INT(i), Nil);
      }
      else if (1 == sscanf(text, "%1[A-Za-z_]", buf)) {

        /* Note: SMV identifiers may start with [A-Za-z_] and then
           continue with [A-Za-z0-9_\$#-]. Hence, check for the first
           character being in the smaller set in the if just above and
           then actually read with the larger set below. */

        /* Note: Check for buffer overflow (without letting it happen)
           by allowing to read at most IDBUFSIZE-1 characters. If the
           latter length is reached, then this is already interpreted
           as a buffer overflow. I.e., the maximum allowed id length
           is IDBUFSIZE-2. */

        int res;
        char sscanf_format[31];

        nusmv_assert(IDBUFSIZE >= 3);
        nusmv_assert(IDBUFSIZE - 1 <= 999999999);
        sprintf(sscanf_format, "%%%u[A-Za-z0-9_\\\\$#-] %%n", IDBUFSIZE - 1);

        res = sscanf(text, sscanf_format, buf, &size);
        nusmv_assert(1 == res);
        if (size == IDBUFSIZE - 1) {
          ErrorMgr_rpterr(errmgr,"XML Reader: buffer overflow");
        }

        /* [AT] If complex identifiers are allowed, a loop should be
           here to parse them. */

        text += size;

        if (0 == strcmp(buf, "TRUE")) {
          newNode = new_node(nodemgr,TRUEEXP, Nil, Nil);
        }
        else if (0 == strcmp(buf, "FALSE")) {
          newNode = new_node(nodemgr,FALSEEXP, Nil, Nil);
        }
        else {
          newNode = new_node(nodemgr,ATOM, (node_ptr) UStringMgr_find_string(strings,buf), Nil);
        }
      }
      else {
        ErrorMgr_rpterr(errmgr,"Invalid constant in type");
      }

      /* Skip comma or final parenthesis. */
      if (',' == text[0]) {
        size = -1;
        sscanf(text, ", %n", &size);
        if (-1 == size) ErrorMgr_rpterr(errmgr,"Incorrect XML file (comma)");
        text += size;
      }
      else if ('}' == text[0]) {
        size = -1;
        sscanf(text, "} %n", &size);
        if (-1 == size) ErrorMgr_rpterr(errmgr,"Incorrect XML file (right cbrace)");
        text += size;
        end = true;
      }
      else ErrorMgr_rpterr(errmgr,"Invalid constant list in type");

      listOfVals = cons(nodemgr,newNode, listOfVals);
    } /* while */

    if (text[0] != '\0') ErrorMgr_rpterr(errmgr,"Incorrect XML file (list of type constants)");

    return new_node(nodemgr,SCALAR, listOfVals, Nil);
  }
  /* Arrays */
  else if (0 == strncmp(text, "array", 5)) {
    text += 5;
    size = -1;
    if (1 == sscanf(text, "%d %n", &i1, &size)) {
      if (-1 == size) {
        ErrorMgr_rpterr(errmgr,"00 Incorrect XML file array %%d .. %%d type");
      }
      text += size;
      size = -1;
      sscanf(text, ".. %n", &size);
      if (-1 == size) {
        ErrorMgr_rpterr(errmgr,"01 Incorrect XML file array %%d .. %%d type");
      }
      text += size;
      size = -1;
      if (1 == sscanf(text, "%d %n", &i2, &size)) {
        if (-1 == size) {
          ErrorMgr_rpterr(errmgr,"02 Incorrect XML file array %%d .. %%d type");
        }
        text += size;
        size = -1;
        sscanf(text, "of %n", &size);
        if (-1 == size) {
          ErrorMgr_rpterr(errmgr,"03 Incorrect XML file array %%d .. %%d type");
        }
        text += size;
        return new_node(nodemgr,ARRAY_TYPE,
                        new_node(nodemgr,TWODOTS,
                                 new_node(nodemgr,NUMBER, NODE_FROM_INT(i1), Nil),
                                 new_node(nodemgr,NUMBER, NODE_FROM_INT(i2), Nil)),
                        game_xml_reader_parse_type(env,text));
      }
      else ErrorMgr_rpterr(errmgr,"04 Incorrect XML file array %%d .. %%d type");
    }
    else ErrorMgr_rpterr(errmgr,"05 Incorrect XML file array %%d .. %%d type");
  }
  else {
    ErrorMgr_rpterr(errmgr,"Incorrect XML file (unknown type : \"%s\")", text);
    return Nil;
  }

  nusmv_assert(false); /* impossible code */

  return Nil;
}

/**Function********************************************************************

  Synopsis    [ This funtion takes a string (tag name) and returns its ID
                (enum). ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static enum XmlTags game_xml_reader_identify_tag(const char* txt)
{
  if (0 == strcmp(txt, "project")) return XML_PROJECT;
  if (0 == strcmp(txt, "signals")) return XML_SIGNALS;
  if (0 == strcmp(txt, "requirements")) return XML_REQUIREMENTS;
  if (0 == strcmp(txt, "property_synthesis")) return XML_PROPERTY_SYNTHESIS;
  if (0 == strcmp(txt, "property_simulation")) return XML_PROPERTY_SIMULATION;
  if (0 == strcmp(txt, "property_assurance")) return XML_PROPERTY_ASSURANCE;
  if (0 == strcmp(txt, "possibilities")) return XML_POSSIBILITIES;
  if (0 == strcmp(txt, "assertions")) return XML_ASSERTIONS;
  if (0 == strcmp(txt, "signal")) return XML_SIGNAL;
  if (0 == strcmp(txt, "kind")) return XML_KIND;
  if (0 == strcmp(txt, "toggled")) return XML_TOGGLED;
  if (0 == strcmp(txt, "requirement")) return XML_REQUIREMENT;
  if (0 == strcmp(txt, "possibility")) return XML_POSSIBILITY;
  if (0 == strcmp(txt, "assertion")) return XML_ASSERTION;
  if (0 == strcmp(txt, "name")) return XML_NAME;
  if (0 == strcmp(txt, "property")) return XML_PROPERTY;
  if (0 == strcmp(txt, "status")) return XML_STATUS;
  if (0 == strcmp(txt, "notes")) return XML_NOTES;
  if (0 == strcmp(txt, "type")) return XML_TYPE;
  if (0 == strcmp(txt, "editable")) return XML_EDITABLE;
  if (0 == strcmp(txt, "active_view")) return XML_ACTIVE_VIEW;
  if (0 == strcmp(txt, "categories")) return XML_CATEGORIES;
  if (0 == strcmp(txt, "category")) return XML_CATEGORY;
  if (0 == strcmp(txt, "trace")) return XML_TRACE;
  if (0 == strcmp(txt, "dependencies")) return XML_DEPENDENCIES;
  if (0 == strcmp(txt, "dependency")) return XML_DEPENDENCY;
  if (0 == strcmp(txt, "loops")) return XML_LOOPS;
  if (0 == strcmp(txt, "creation_info")) return XML_CREATION_INFO;
  if (0 == strcmp(txt, "stripe")) return XML_STRIPE;
  if (0 == strcmp(txt, "step")) return XML_STEP;
  if (0 == strcmp(txt, "value")) return XML_VALUE;
  if (0 == strcmp(txt, "base_automaton_name")) return XML_BASE_AUTOMATON_NAME;
  if (0 == strcmp(txt, "automaton_parameter")) return XML_AUTOMATON_PARAMETER;
  if (0 == strcmp(txt, "automata")) return XML_AUTOMATA;
  if (0 == strcmp(txt, "auto_signal")) return XML_AUTO_SIGNAL;
  return XML_ERROR;
}

/**Function********************************************************************

  Synopsis    [ This function is called when parser encounter start of
                some tag. ]

  Description [ This function simply adds a new node (with the element
                tag) at the stack. Also a list of tags that are
                ignored is defined here. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_xml_reader_tag_begin(NuSMVEnv_ptr env,
                                      void* data,
                                      const char* name,
                                      const char** atts)
{
  XmlParseResult_ptr parseResult = XML_PARSE_RESULT(data);

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings =  USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  /* Simply create a new node at the stack with the given element name. */
  enum XmlTags tag = game_xml_reader_identify_tag(name);

  /* Reset line info for possible error messages. */
  yylineno = XML_GetCurrentLineNumber(parseResult->parser);

  /* Some higher level tag is ignored, so ignore everything until the
     corresponding end tag is met.
  */
  if (parseResult->isIgnore) return;

  switch (tag) {
  /* Tags that cannot be met. */
  case XML_ERROR:
  case XML_TEXT:
    ErrorMgr_rpterr(errmgr,"Unexpected XML element: tag \"%s\"", name);

  /* Tags we are interested in. */
  case XML_PROJECT:
  case XML_SIGNALS:
  case XML_REQUIREMENTS:

  case XML_SIGNAL:
  case XML_KIND:
  case XML_TOGGLED:
  case XML_REQUIREMENT:
  case XML_PROPERTY:

  case XML_NAME:
  case XML_STATUS:
  case XML_TYPE:

    /* No attributes are allowed. */
    if (atts[0] != NULL) {
      ErrorMgr_rpterr(errmgr,"Unexpected XML element attribute: %s", atts[0]);
    }

    parseResult->stack = cons(nodemgr,new_node(nodemgr,tag, Nil, Nil), parseResult->stack);
    return;

  /* Tags which are to be ignored. */
  case XML_PROPERTY_SYNTHESIS:
  case XML_PROPERTY_SIMULATION:
  case XML_PROPERTY_ASSURANCE:

  case XML_POSSIBILITIES:
  case XML_ASSERTIONS:

  case XML_POSSIBILITY:
  case XML_ASSERTION:

  case XML_EDITABLE:
  case XML_ACTIVE_VIEW:

  case XML_CATEGORIES:
  case XML_CATEGORY:
  case XML_TRACE:

  case XML_DEPENDENCIES:
  case XML_DEPENDENCY:

  case XML_LOOPS:

  case XML_CREATION_INFO:

  case XML_STRIPE:
  case XML_STEP:
  case XML_VALUE:

  case XML_BASE_AUTOMATON_NAME:
  case XML_AUTOMATON_PARAMETER:
  case XML_AUTOMATA:
  case XML_AUTO_SIGNAL:

  case XML_NOTES:
    parseResult->stack = cons(nodemgr,new_node(nodemgr,tag, Nil, Nil), parseResult->stack);
    parseResult->isIgnore = true;
    return;
  } /* switch */

  ErrorMgr_rpterr(errmgr,"Unknown XML element: tag \"%s\"", name);

  return;
}

/**Function********************************************************************

  Synopsis    [ This function is called when the end of any tag is
                encountered by the parser. ]

  Description [ The function pops the nodes from the stack until the
                node corresponding to "name", checks the required
                constraints and stores the obtained structures to the
                fields of "data" (XmlParseResult). All the
                correponding allocated memory is freed. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_xml_reader_tag_end(NuSMVEnv_ptr env,void* data, const char *string)
{
  XmlParseResult_ptr parseResult = XML_PARSE_RESULT(data);

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings =  USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  enum XmlTags tag = game_xml_reader_identify_tag(string);

  /* Reset line info for possible error messages. */
  yylineno = XML_GetCurrentLineNumber(parseResult->parser);

  /* Some higher level tag is ignored, so ignore everthing until
     corresponding end-tag is met.
  */
  if (parseResult->isIgnore) {
    if (node_get_type(car(parseResult->stack)) == tag) {
      /* The corresponding end tag is met. */
      node_ptr node = game_xml_reader_pop_stack(nodemgr,&parseResult->stack);
      free_node(nodemgr,node);
      parseResult->isIgnore = false;
    }
    return;
  }

  switch (tag) {
  /* Impossible situation. */
  case XML_ERROR:
  case XML_TEXT:
    ErrorMgr_rpterr(errmgr,"Unexpected end XML (%s) tag", string);
    break;

  /* All signals, requirements, etc are processed when they are met
     => just pop one element (and check its tag).
  */
  case XML_PROJECT:
  case XML_SIGNALS:
  case XML_REQUIREMENTS:
    {
      node_ptr node = game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      nusmv_assert(node_get_type(node) == tag &&
                   Nil == car(node) &&
                   Nil == cdr(node) /* nothing to free */);
      free_node(nodemgr,node);
    }
    break;

  /* Input and output signals: only name, kind and type elements can
     be inside (both already processed, i.e., with end tag met). So
     create a proper var definition and add it to the corresponding
     list. Notes elemenets are ignored.
  */
  case XML_SIGNAL:
    {
      node_ptr name, kind, type, signal;

      type = game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      kind = game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      name = game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      signal = game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);

      if (node_get_type(name) != XML_NAME) {
        swap_nodes(&name, &type);
        if (node_get_type(name) != XML_NAME) {
          swap_nodes(&name, &kind);
        }
      }
      if (node_get_type(kind) != XML_KIND) {
        swap_nodes(&type, &kind);
      }

      nusmv_assert(node_get_type(name) == XML_NAME &&
                   node_get_type(kind) == XML_KIND &&
                   node_get_type(type) == XML_TYPE &&
                   node_get_type(signal) == tag);
      /* End tags of NAME, KIND and TYPE are met. */
      nusmv_assert(car(name) != Nil && car(kind) != Nil && car(type) != Nil);

      free_node(nodemgr,signal);
      signal = new_node(nodemgr,COLON, car(name), car(type));

      if ('E' == PTR_TO_INT(car(kind))) {
        parseResult->input_vars = cons(nodemgr,signal, parseResult->input_vars);
      }
      else if ('S' == PTR_TO_INT(car(kind))) {
        parseResult->output_vars = cons(nodemgr,signal, parseResult->output_vars);
      }
      else {
        ErrorMgr_rpterr(errmgr,"The value of kind of a signal can only be E or S (found: %c).",
               PTR_TO_INT(car(kind)));
      }

      free_node(nodemgr,name);
      free_node(nodemgr,kind);
      free_node(nodemgr,type);
    }
    break;

  /* Assumption and guarantee requirements can have only NAME, KIND
     and PROPERTY (NOTES were ignored).
  */
  case XML_REQUIREMENT:
    {
      /* Pop the NAME and PROPERTY nodes, and the node of assumption or
         guarantee */
      node_ptr name =
        game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      node_ptr property =
        game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      node_ptr kind =
        game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      node_ptr toggled =
        game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);
      node_ptr requirement =
        game_xml_reader_pop_stack_cleanly(nodemgr,&parseResult->stack);;

      /* Swap the elements if required. */
      if (node_get_type(name) != XML_NAME) {
        swap_nodes(&name, &property);
        if (node_get_type(name) != XML_NAME) {
          swap_nodes(&name, &kind);
          if (node_get_type(name) != XML_NAME) {
            swap_nodes(&name, &toggled);
          }
        }
      }
      if (node_get_type(property) != XML_PROPERTY) {
        swap_nodes(&property, &kind);
        if (node_get_type(property) != XML_PROPERTY) {
          swap_nodes(&property, &toggled);
        }
      }
      if (node_get_type(kind) != XML_KIND) {
        swap_nodes(&kind, &toggled);
      }

      nusmv_assert(node_get_type(name) == XML_NAME &&
                   node_get_type(property) == XML_PROPERTY &&
                   node_get_type(kind) == XML_KIND &&
                   node_get_type(toggled) == XML_TOGGLED &&
                   node_get_type(requirement) == tag);

      /* Their end tags were met. */
      nusmv_assert(car(name) != Nil
                   && car(property) != Nil
                   && car(kind) != Nil
                   && car(toggled) != Nil);

      /* If a requirement is toggled on then process it (otherwise
         ignore it). */
      if ('1' == PTR_TO_INT(car(toggled))) {
        if ('A' == PTR_TO_INT(car(kind))) {
          parseResult->assumptions = new_node(nodemgr,AND,
                                              car(property),
                                              parseResult->assumptions);
        }
        else if ('G' == PTR_TO_INT(car(kind))) {
          parseResult->guarantees = new_node(nodemgr,AND,
                                             car(property),
                                             parseResult->guarantees);
        }
        else {
          ErrorMgr_rpterr(errmgr,"The value of kind of a requirement can only be A or G "
                 "(found: %c).",
                 PTR_TO_INT(car(kind)));
        }
      }
      else {
        /*toggled can be '0' or '1' only*/
        nusmv_assert('0' == PTR_TO_INT(car(toggled)));
      }

      /* Free all the obtained nodes from the stack (and their
         children if required). */
      free_node(nodemgr,car(name));
      free_node(nodemgr,name);
      free_node(nodemgr,property);
      free_node(nodemgr,kind);
      free_node(nodemgr,toggled);
      free_node(nodemgr,requirement);
    }
    break;

  /* Only XML_TEXT should be on the stack. For NAME and STATUS,
     convert text to ATOM and made it left child of given tag. For
     KIND make left child an integer with possible values 'A', 'G',
     'E', 'S'. For TOGGLED make left child an integer with possible
     values '0' and '1'.
  */
  case XML_NAME:
  case XML_STATUS:
  case XML_KIND:
  case XML_TOGGLED:
    {
      node_ptr text;

      /* Pop the TEXT node. Use the simple pop_stack function! */
      text = game_xml_reader_pop_stack(nodemgr,&parseResult->stack);

      nusmv_assert(node_get_type(text) == XML_TEXT);

      nusmv_assert(node_get_type(car(parseResult->stack)) == tag
                   /* end tag has been already met */
                   && caar(parseResult->stack) == Nil);

      if (XML_NAME == tag || XML_STATUS == tag) {
        /* Create left child for the tag node as usual NuSMV ATOM. */
        setcar(car(parseResult->stack),
               new_node(nodemgr,ATOM, (node_ptr) UStringMgr_find_string(strings,(char*) car(text)), Nil));
      }
      else if (XML_KIND == tag) {
        /* Set left child to be an integer 'A', 'G', 'E' or 'S'. */
        int c;
        if (0 == strcmp((char*) car(text), "A")) c = 'A';
        else if (0 == strcmp((char*) car(text), "G")) c = 'G';
        else if (0 == strcmp((char*) car(text), "E")) c = 'E';
        else if (0 == strcmp((char*) car(text), "S")) c = 'S';
        else {
          ErrorMgr_rpterr(errmgr,"A kind can be only: A, G, E and S (found: %s).", car(text));
        }
        setcar(car(parseResult->stack), NODE_FROM_INT(c));
      }
      else if (XML_TOGGLED == tag) {
        int i;
        if (0 == strcmp((char*) car(text), "0")) i = '0';
        else if (0 == strcmp((char*) car(text), "1")) i = '1';
        else {
          ErrorMgr_rpterr(errmgr,"The value of toggled can be only: 0 and 1 (found: %s).",
                 car(text));
        }
        setcar(car(parseResult->stack), NODE_FROM_INT(i));
      }
      else {
        ErrorMgr_internal_error(errmgr,"impossible code");
      }

      game_xml_reader_free_text_node(nodemgr,text);
    }
    break;

  /* PROPERTY can contain only a TEXT (with a formula). */
  case XML_PROPERTY:
    {
      const char* arg[1];
      node_ptr property;

      /* Pop the TEXT node and parse it with the NuGaT parser. Use the
         usual pop_stack function. */
      node_ptr node = game_xml_reader_pop_stack(nodemgr,&parseResult->stack);

      nusmv_assert(node_get_type(node) == XML_TEXT &&
                   node_get_type(car(parseResult->stack)) == XML_PROPERTY &&
                   /* this is first met end-tag */
                   caar(parseResult->stack) == Nil);

      /* Get and parse the string. */
      arg[0] = (char*) car(node);
      if (Parser_read_psl_from_string(1, arg, &property)) {
        ErrorMgr_rpterr(errmgr,"Parse error in an PSL expression in XML file");
      }

      game_xml_reader_free_text_node(nodemgr,node);
      setcar(car(parseResult->stack), property);
    }
    break;

  case XML_TYPE:
    {
      /* Only XML_TEXT should be at stack. Convert text
         to proper type and made it left child of XML_TYPE */

      /* Pop the TEXT node. Use the usual pop_stack function! */
      node_ptr text = game_xml_reader_pop_stack(nodemgr,&parseResult->stack);
      nusmv_assert(node_get_type(text) == XML_TEXT);

      if (parseResult->stack == Nil ||
          node_get_type(car(parseResult->stack)) != XML_TYPE ||
          caar(parseResult->stack) != Nil /* end tag has been already met */) {
        ErrorMgr_rpterr(errmgr,"Incorrect XML file (tag %s)", string);
      }

      /* Create left child for NAME node as usual NuSMV ATOM. */
      setcar(car(parseResult->stack),
             game_xml_reader_parse_type(env,(char*) car(text)));

      game_xml_reader_free_text_node(nodemgr,text);
    }
    break;

  /* These tags are ignored at the moment and cannot be met here. */

  case XML_PROPERTY_SYNTHESIS:
  case XML_PROPERTY_SIMULATION:
  case XML_PROPERTY_ASSURANCE:

  case XML_POSSIBILITIES:
  case XML_ASSERTIONS:

  case XML_POSSIBILITY:
  case XML_ASSERTION:

  case XML_EDITABLE:
  case XML_ACTIVE_VIEW:

  case XML_CATEGORIES:
  case XML_CATEGORY:
  case XML_TRACE:

  case XML_DEPENDENCIES:
  case XML_DEPENDENCY:

  case XML_LOOPS:

  case XML_CREATION_INFO:

  case XML_STRIPE:
  case XML_STEP:
  case XML_VALUE:

  case XML_BASE_AUTOMATON_NAME:
  case XML_AUTOMATON_PARAMETER:
  case XML_AUTOMATA:
  case XML_AUTO_SIGNAL:

  case XML_NOTES:

    ErrorMgr_rpterr(errmgr,"Impossible end tag (%s)", string);
    break;

  } /* switch */

  return;
}

/**Function********************************************************************

  Synopsis    [ This function is called when a character string is
                encountered by the parser. ]

  Description [ This function simply adds a new node (with XML_TEXT
                tag and the text) at the stack. The input string is
                cleaned up, i.e., the white spaces at the beginning
                and the end are removed.

                Note: the memory from the text has to be deallocated
                      later by the invoker. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_xml_reader_char_handler(NuSMVEnv_ptr env,void* data, const char *txt, int len)
{
  XmlParseResult_ptr parseResult = XML_PARSE_RESULT(data);
  int prevLen;
  node_ptr text_node;
  char* buffer;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings =  USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  /* Reset line info for possible error messages. */
  yylineno = XML_GetCurrentLineNumber(parseResult->parser);

  /* If XML elements being parsed are ignored, ignore also the text. */
  if (parseResult->isIgnore) return;

  /* Clean up the input string, i.e., removed white spaces at the
     beginning and the end. */
  while (len > 0 && isspace(txt[0])) {
    ++txt;
    --len;
  };
  while (len > 0 && isspace(txt[len-1])) {
    --len;
  };

  /* Create a special new element XML_TEXT to put text on the stack.
     If there is already an XML_TEXT at the stack, the left child must
     be reallocated to hold the concatenation of the previous text and
     this one.
  */

  if (Nil != parseResult->stack &&
      node_get_type(car(parseResult->stack)) == XML_TEXT) {
    text_node = car(parseResult->stack);
    /* Optimisation: if text is an empty string then do nothing. */
    if (0 == len) return;
  }
  else {
    text_node = new_node(nodemgr,XML_TEXT, Nil, Nil);
    parseResult->stack = cons(nodemgr,text_node, parseResult->stack);
  }

  buffer = (char*) car(text_node);
  prevLen = buffer != NULL ? strlen(buffer) : 0;
  buffer = REALLOC(char, buffer,  prevLen + len + 1);
  if (!buffer) ErrorMgr_error_out_of_memory(errmgr,len + 1);

  strncpy(buffer + prevLen, txt, len);
  buffer[prevLen+len] = '\0';

  setcar(text_node, (node_ptr) buffer);

  return;
}

/**Function********************************************************************

  Synopsis    [ Constructor for XmlParseResult. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ gameXmlReader_XmlParseResult_destroy ]

******************************************************************************/
static XmlParseResult_ptr gameXmlReader_XmlParseResult_create(const ErrorMgr_ptr errmgr,XML_Parser parser)
{
  XmlParseResult_ptr self;

  self = ALLOC(XmlParseResult, 1);
  if (XML_PARSE_RESULT(NULL) == self) ErrorMgr_error_out_of_memory(errmgr,0);

  self->input_vars = Nil;
  self->output_vars = Nil;
  self->assumptions = Nil;
  self->guarantees = Nil;
  self->parser = parser;
  self->isIgnore = false;
  self->stack = Nil;

  return self;
}

/**Function********************************************************************

  Synopsis    [ Destroys XmlParseResult.parser. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ gameXmlReader_XmlParseResult_destroy ]

******************************************************************************/
static void gameXmlReader_XmlParseResult_destroy_parser(XmlParseResult_ptr self)
{
  nusmv_assert((XML_Parser) NULL != self->parser);

  XML_ParserFree(self->parser);
  self->parser = (XML_Parser) NULL;
}

/**Function********************************************************************

  Synopsis    [ Destructor for XmlParseResult. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ gameXmlReader_XmlParseResult_create ]

******************************************************************************/
static void gameXmlReader_XmlParseResult_destroy(XmlParseResult_ptr self)
{
  self->input_vars = Nil;
  self->output_vars = Nil;
  self->assumptions = Nil;
  self->guarantees = Nil;
  if ((XML_Parser) NULL != self->parser) {
    XML_ParserFree(self->parser);
    self->parser = (XML_Parser) NULL;
  }
  self->isIgnore = false;
  self->stack = Nil;
  FREE(self);
}

/*****************************************************************************/

#endif /* HAVE_LIBEXPAT */
