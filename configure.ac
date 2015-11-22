-*- mode: m4 -*-
#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script. (configure,config.h,config.h.in,config.status)
AC_PREREQ(2.57)

AC_INIT(NuGaT, 0.5.0, nugat@list.fbk.eu)

# local configuration
nusmv_config_dir=nusmv-config
nusmv_pkg=nusmv-2.pc

# where to look for install.sh and other helpers
AC_CONFIG_AUX_DIR(helpers)

AM_INIT_AUTOMAKE(NuGaT, $PACKAGE_VERSION)

AC_CANONICAL_HOST

AC_CONFIG_SRCDIR([config.h.in])
AM_CONFIG_HEADER([config.h])

AC_DEFINE_UNQUOTED(PACKAGE_BUILD_DATE, "`date -u`", Build date)

# version
NUGAT_MAJ_VER=`echo $PACKAGE_VERSION | cut -d. --fields="1 2"`
AC_SUBST(NUGAT_MAJ_VER)

# Arguments

# libraries are static by default. User can override by passing 
# the flag --enable-dynamic
AC_DISABLE_SHARED


# Extra packages that must be built and distributed
extra_pkgs=

# default addons
def_addons=game
AC_ARG_ENABLE(addons, 
  [  --enable-addons  Builds given addons. Enabled addon names must be colon-separated (:)],
  [ if test "x$enableval" = "xno"; then 
     addons=
    else 
      if test "x$enableval" = "xyes"; then
        addons=all
      else addons=$enableval
      fi
    fi],
  [ addons=$def_addons ])


# If the LTL2SMV program must be generated:
AC_ARG_ENABLE(ltl2smv,
  [  --enable-ltl2smv  Builds the executable ltl2smv (default is yes)], 
  [if test "x$enableval" = "xno"; then 
    enable_ltl2smv=no
fi], [enable_ltl2smv=yes])
AM_CONDITIONAL(HAVE_LTL2SMV, test "x$enable_ltl2smv" != "xno")


# Executables are statically created
opt_static_link=no
AC_ARG_ENABLE(static-link, AC_HELP_STRING([--enable-static-link], [link all executables statically]), opt_static_link=$enableval)

# nusmv dir:
nusmvdefpath1=../nusmv
nusmvdefpath2=../NuSMV-2.5.0/nusmv
AC_ARG_WITH(nusmv-dir,
[  --with-nusmv-dir=<dir> The directory which NuSMV is contained in. 
			      (default is ../nusmv)],
[ if test -x $withval; then 
    nusmv_dir=`cd $withval && pwd`
  else
    nusmv_dir=$withval
  fi],
[ if test -x $nusmvdefpath1; then 
    nusmv_dir=`cd $nusmvdefpath1 && pwd`
  else
    if test -x $nusmvdefpath2; then
      nusmv_dir=`cd $nusmvdefpath2 && pwd`
    else
      nusmv_dir=
    fi
  fi])

expatdefpath=/usr

# readline (linking with readline may be disabled by the user)
AC_ARG_ENABLE(expat,
[  --enable-expat    Links NuGaT with expat library (default is yes when found)],
  [if test "x$enableval" = "xyes"; then
    enable_expat=yes
   fi
   if test "x$enableval" = "xno"; then 
    enable_expat=no
   fi], [enable_expat=yes])

# expat library dir:
AC_ARG_WITH(expat-libdir,
[  --with-expat-libdir=<dir> The directory which the expat library is contained in. 
			      (default is /usr/lib)],
[expatlibdir=-L$withval], [expatlibdir=])

# expat library header dir:
AC_ARG_WITH(expat-incdir,
  [  --with-expat-incdir=<dir> The directory which the expat.h header is contained in. 
			      (default are standard locations)],
  [ expatincdir=$withval
    if ! test -f $expatincdir/expat.h; then
        AC_MSG_ERROR(The expat.h header file has not been found in "$expatincdir".
See configure option --with-expat-incdir to specify where the header file is located.)
    else 
     expat_h_found=yes
     expatuserinc="-L $expatincdir"
    fi
  ], 
  [ expatuserinc=""
    AC_CHECK_HEADER(expat.h, 
      [expat_h_found=yes],
      [])
  ])
AC_SUBST(expatuserinc)


# readline (linking with readline may be disabled by the user)
AC_ARG_ENABLE(readline,
[  --enable-readline    Links NuGaT with readline library (default is yes)],
  [if test "x$enableval" = "xyes"; then
    enable_readline=yes
   fi
   if test "x$enableval" = "xno"; then 
    enable_readline=no
   fi], [enable_readline=yes])

excflags=""
AC_ARG_ENABLE(profiling,
  [  --enable-profiling  Builds the system with profiling information (default no)], 
  [if test "x$enableval" = "xyes"; then 
    excflags="-pg "
fi], [])

AC_ARG_ENABLE(pedantic,
  [  --enable-pedantic  Builds the system with pedantic warning (default no)], 
  [if test "x$enableval" = "xyes"; then 
    excflags="-Wall -pedantic $excflags"
fi], [])


# Checks for programs.
oldcflags=$CFLAGS
AC_PROG_CC
AM_PROG_CC_C_O
AC_PROG_CPP
AC_PROG_CXX
AC_PROG_CXXCPP
CFLAGS="$excflags$oldcflags"

if test "x$ac_cv_prog_CPP" != "x"; then
AC_DEFINE(HAVE_CPP, 1, Have preprocessor)
AC_DEFINE_UNQUOTED(PROG_CPP, $ac_cv_prog_CPP -x c, Preprocessor call string)
else
AC_DEFINE(HAVE_CPP, 0, Have preprocessor)
fi

AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_LIBTOOL
AC_PROG_YACC
AM_PROG_LEX

if test "$LEX" != flex; then
  LEX="$SHELL $missing_dir/missing flex"
  AC_SUBST(LEX_OUTPUT_ROOT, lex.yy)
  AC_SUBST(LEXLIB, '')
  if test "x$LEX" == "x"; then
    AC_MSG_ERROR("Working lex or flex are required to build NuGaT.")
  fi
fi

AC_PATH_PROG(PERL, perl, perl_is_missing)
AC_CHECK_PROGS(HTMLDUMP, lynx links, lynx_or_links_is_missing)

AC_PATH_PROG(LATEX, latex)
AM_CONDITIONAL(HAVE_LATEX, test "x$LATEX" != "x")

AC_PATH_PROG(PDFLATEX, pdflatex)
AC_PATH_PROG(EPSTOPDF, epstopdf)
AC_PATH_PROG(PDFTOPS, pdftops)
AM_CONDITIONAL(HAVE_PDFLATEXETAL, test "x$PDFLATEX" != "x" -a "x$EPSTOPDF" != "x" -a "x$PDFTOPS" != "x")
if test "x$PDFLATEX" != "x" -a "x$EPSTOPDF" != "x" -a "x$PDFTOPS" != "x"; then
IF_USE_PACKAGE_HYPERREF='\iftrue'
else
IF_USE_PACKAGE_HYPERREF='\iffalse'
fi
AC_SUBST(IF_USE_PACKAGE_HYPERREF)

# features
AC_CPP_FUNC

# Checks for dirs and files
AC_MSG_CHECKING(Configured dirs)
for d in $nusmv_dir; do
  if ! test -d $d; then
      AC_MSG_ERROR(Directory $d not found. See configure option --with-nusmv-dir)
  fi
done
AC_MSG_RESULT(ok)
AC_MSG_CHECKING(Configured files)
for f in $nusmv_config_dir/$nusmv_pkg; do
  if ! test -f $f; then
      AC_MSG_ERROR(File $f not found. See configure option --with-nusmv-dir)
  fi
done
AC_MSG_RESULT(ok)
AC_SUBST(nusmv_dir)

AC_PATH_PROG(PKG_CONFIG, [pkg-config], [no])
if test x$PKG_CONFIG = xno ; then
  AC_MSG_ERROR([*** pkg-config not found. See http://www.freedesktop.org/software/pkgconfig/])
fi

cuddname=`$PKG_CONFIG --variable=cuddname $nusmv_config_dir/$nusmv_pkg`
AC_SUBST(cuddname)

# cudd dir:
AC_ARG_WITH(cudd-dir,
[  --with-cudd-dir=<dir> The directory which CuDD is contained in. 
			      (default is parallel to the NuSMV directory)],
[cudd_dir=$withval], [cudd_dir=$nusmv_dir/../$cuddname])
AC_MSG_CHECKING(Configured cudd dir)
for d in $cudd_dir; do
  if ! test -d $d; then
      AC_MSG_ERROR(Directory $d not found. See configure option --with-cudd-dir)
  fi
done
for f in $cudd_dir/cudd/cudd.h; do
  if ! test -f $f; then
      AC_MSG_ERROR(File $d not found. See configure option --with-cudd-dir)
  fi
done
AC_MSG_RESULT(ok)
AC_SUBST(cudd_dir)

# portability issues
AC_CHECK_SIZEOF([void *])
AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([long])
AC_CHECK_SIZEOF([long long])


# Checks for libraries.

AC_CHECK_LIB([m], [exp])

# For readline:
# if readline is enabled, then:
# 1. chooses either ncurses, curses or termcap to be linked to readline
# 2. checks readline with the library selected in 1
# 3. uses the internal readline if 2 fails
if test "x$enable_readline" = "xyes"; then
AC_CHECK_LIB([ncurses], [main], [ac_termcap_lib=-lncurses], \
  [AC_CHECK_LIB([curses], [main], [ac_termcap_lib=-lcurses], \
     [AC_CHECK_LIB([termcap], [main], [ac_termcap_lib=-ltermcap], \
        [ac_termcap_lib=])])])
fi

if test "x$enable_readline" = "xyes"; then
if test x$ac_termcap_lib == x; then
   AC_MSG_WARN(cannot find a library to link with readline (next step might fail))
fi
fi

if test "x$enable_readline" = "xyes"; then
AC_CHECK_LIB([readline], [readline], \
   [AC_DEFINE(HAVE_LIBREADLINE, 1, Uses the system readline)
    readline_libs="-lreadline $ac_termcap_lib"], \
   [AC_DEFINE(HAVE_LIBREADLINE, 0, Uses the private readline)
    readline_libs="";\
    AC_MSG_WARN(cannot link readline: NuGaT will use an internal version)], \
   [$ac_termcap_lib])	
else
   readline_libs=
fi
AC_SUBST(readline_libs)

# expat library
if test x$expat_h_found == xyes -a x$enable_expat ==  xyes; then
LIBS_old=$LIBS
AC_CHECK_LIB(expat, XML_ParserCreate, 
   [ac_have_expat=yes
    AC_DEFINE(HAVE_LIBEXPAT, 1, Enables expat usage)
    expat_libs="$expatlibdir -lexpat"
    ],
   [ac_have_expat=no
    AC_DEFINE(HAVE_LIBEXPAT, 0, Disables expat usage)
    expat_libs=
    ], 
   [$expatlibdir])    
LIBS="$LIBS_old -L/home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/build/build-cudd/lib -lcudd -lutil -lmtr -lst -lreadline -ltermcap /usr/lib/x86_64-linux-gnu/libexpat.la -lm "

else 
  expat_libs=
  ac_have_expat=no
fi

AC_SUBST(expat_libs)		      

AM_CONDITIONAL(HAVE_LIBEXPAT, test "x$ac_have_expat" = "xyes")
AC_SUBST(HAVE_LIBEXPAT)


# Hopefully this will be no longer needed in the future

# Sat solvers?
have_sat_solvers=`$PKG_CONFIG --variable=sat_available $nusmv_config_dir/$nusmv_pkg`
if test "x$have_sat_solvers" = "xyes"; then
   AC_DEFINE(HAVE_SAT_SOLVER, 1, Have at least one sat solver)
else 
   AC_DEFINE(HAVE_SAT_SOLVER, 0, No sat solvers available)
fi

# zchaff?
have_solver_zchaff=$(grep -c "define NUSMV_HAVE_SOLVER_ZCHAFF 1" $nusmv_dir/build/nusmv-config.h)
if test "x$have_solver_zchaff" = "x1"; then
   AC_DEFINE(HAVE_SOLVER_ZCHAFF, 1, Have zchaff)
else 
   AC_DEFINE(HAVE_SOLVER_ZCHAFF, 0, Dont have zchaff)
fi

# minisat?
have_solver_minisat=$(grep -c "define NUSMV_HAVE_SOLVER_MINISAT 1" $nusmv_dir/build/nusmv-config.h)
if test "x$have_solver_minisat" = "x1"; then
   AC_DEFINE(HAVE_SOLVER_MINISAT, 1, Have minisat)
else 
   AC_DEFINE(HAVE_SOLVER_MINISAT, 0, Dont have minisat)
fi

AC_DEFINE(HAVE_EXTERN_ARGS_MACROS, 1, Define to 1 if the system has EXTERN and ARGS)

# ======================================================================
#                          Addons checking
#                              -------
AC_MSG_CHECKING(for Addons)

# The list of all available addons
all_addons="game"

# The list of addons that when required should be configured but
# not built. This rules does not apply when the addon is required
# as a dependency.
not_built_addons=

# The list of meta-addons, that do not need to have a
# corresponding entry in src/addons, i.e. they are not actually
# required to exist in a separate directory inside src/addons like
# normal addons.
# Still meta-addons need to be configured as the source code
# contains sections that are conditioned to them, or they can be
# used as aliases that trigger the building of a set of
# other dependecies. 
meta_addons=


# ----------------------------------
# Dependencies among addons:
game_deps=

# ----------------------------------


# ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
_bs_addons=`echo "$addons" | $SED -e 's/:/ /g'` # blank-separated addons
found_addons=
notfound_addons=
alias_addons=

# check for 'all'
if test "x$_bs_addons" = "xall"; then
  _bs_addons=$all_addons
fi

# checking distributed addons are available
for addon in $_bs_addons
do
  if test -d src/addons/$addon; then
    found_addons="$addon $found_addons"
  else
    if test "x$(echo $all_addons | grep -w $addon -)" == "x"; then
      AC_MSG_ERROR(Addon '$addon' does not exist)
    else
      if test "x(echo $meta_addons | grep -w $addon -)" == "x"; then
         notfound_addons="$addon $notfound_addons"
      else
         alias_addons="$addon $alias_addons"
      fi
    fi
  fi
done

dep_addons=
function addon_calc_dep() # calculates dependencies of given addon
{
  addon=$1
  __addon_deps=${addon}_deps
  deps=${!__addon_deps}
  
  for dep in $deps; do
    _tmp=$(echo "$dep_addons $found_addons $alias_addons" | grep -w $dep -) # already taken?
    if test "x$_tmp" == "x"; then
        dep_addons="$dep $dep_addons"
    fi
    addon_calc_dep $dep    
  done
}

# Dependency tracking
for addon in $found_addons $alias_addons; do
  addon_calc_dep $addon
done

# All other possible specific checkings for addons:
for addon in $found_addons $dep_addons $alias_addons; do
  case $addon in
  game) ;;
  *) 
    AC_MSG_ERROR("Addon $addon is not supported");;
  esac
done

if test "x$notfound_addons" == "x"; then
  AC_MSG_RESULT(ok)
else
  AC_MSG_RESULT(warnings)
fi


# filters out all not built addons, but only if not required as dependecies
all_built_addons=$dep_addons
all_not_built_addons=
for addon in $found_addons; do
    if test "x$(echo $not_built_addons | grep -w $addon -)" == "x"; then
       all_built_addons="$addon $all_built_addons"
    else
       all_not_built_addons="$addon $all_not_built_addons"
    fi
done
AC_SUBST(ADDONS_PKGS, $all_built_addons)


# declares and assigns a set of have_<addon> vars to be used later
for addon in $all_addons; do
  if test "x$(echo "$found_addons $dep_addons $alias_addons" | grep -w $addon -)" == "x"; then
    eval have_addon_${addon}=0
  else eval have_addon_${addon}=1
  fi
done

# Outputs 
for addon in $all_addons; do
  _vname=have_addon_${addon}
  _have_addon=${!_vname}
  case $addon in
  game) 
    if test $_have_addon == 1; then AC_CONFIG_FILES([src/addons/game/Makefile]) fi
    AC_DEFINE_UNQUOTED(HAVE_GAME, $_have_addon, Enables the named addon)
    AM_CONDITIONAL(HAVE_GAME, test $_have_addon = 1);;

  *) 
    AC_MSG_ERROR("Addon $addon is not supported");;
  esac  
done

AC_DEFINE_UNQUOTED(LINKED_ADDONS, "${found_addons}${alias_addons}${dep_addons}", 
  Names of linked addons)


#                              -------
#                       End of Addons checking
# ======================================================================



# Checks for header files.
AC_HEADER_DIRENT
AC_HEADER_STDC
AC_CHECK_HEADERS([float.h limits.h memory.h stddef.h stdlib.h string.h \
  sys/ioctl.h sys/param.h sys/time.h sys/resource.h unistd.h signal.h sys/signal.h \
  errno.h regex.h])

# This is for malloc:
AC_CHECK_HEADER(sys/types.h)
AC_CHECK_HEADER(malloc.h, 
	[ AC_DEFINE(HAVE_MALLOC_H, 1, Defined to 1 if the system provides malloc.h)],
	[ AC_CHECK_HEADER(sys/malloc.h, 
	    [AC_DEFINE(HAVE_SYS_MALLOC_H, 1, Defined to 1 if the system provides sys/malloc.h)],
	    [],
	    [
	      #if HAVE_SYS_TYPES_H
	      # include <sys/types.h>
	      #endif
	    ]  
	    )],
	[
	 #if HAVE_SYS_TYPES_H
	 # include <sys/types.h>
	 #endif
	])


# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_CLOSEDIR_VOID
AC_PROG_GCC_TRADITIONAL
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_FUNC_SETVBUF_REVERSED
AC_TYPE_SIGNAL
AC_FUNC_STAT
AC_FUNC_STRTOD
AC_FUNC_VPRINTF
AC_CHECK_FUNCS([floor memmove memset pow strcasecmp strchr \
		strrchr strstr strtol, random srandom getpid \
		mkstemp mktemp tmpnam getenv setvbuf system popen isatty])

# Executable file names suffix:
AC_DEFINE_UNQUOTED(EXEEXT, "$EXEEXT", Executable file names suffix)

AC_SUBST(EXTRA_PKGS, $extra_pkgs)
                     
AC_CONFIG_FILES([Makefile
                 contrib/Makefile
                 examples/Makefile
                 src/Makefile
                 src/addons/Makefile
                 src/parser/Makefile
                 src/smgame/Makefile
                 test/Makefile
                 ])

if test "$opt_static_link" = yes; then
		LDFLAGS="-all-static ${LDFLAGS}"
fi

# ----------------------------------------------------------------------
# All conditionally distributed packages go here:
# ----------------------------------------------------------------------

AC_OUTPUT

echo

if test "x${found_addons}${notfound_addons}${alias_addons}" != "x"; then
echo ------------------------------------------------------------------ 
echo "Addons"
if test "x${found_addons}${alias_addons}" != "x"; then
  printf "  requested:\t${found_addons}${alias_addons}\n"
fi
if test "x${dep_addons}" != "x"; then
  printf "  dependencies:\t${dep_addons}\n"
fi
if test "x${all_not_built_addons}" != "x"; then
  printf "  not built:\t${all_not_built_addons}\t (although configured)\n"
fi
if test "x${notfound_addons}" != "x"; then
  printf "  unsupported:\t${notfound_addons}\n"
fi
echo ------------------------------------------------------------------ 
fi

if test "x$extra_pkgs" != "x"; then
echo ------------------------------------------------------------------ 
echo "Extra packages: $extra_pkgs"
echo ------------------------------------------------------------------ 
fi

if test "x$expat_h_found" = "xno"; then
echo ------------------------------------------------------------------ 
echo "The expat library has not been found.                            "
echo "See configure options --with-expat-{inc,lib}dir to help "
echo "configure finding expat if it is installed in non-standard paths." 
echo ------------------------------------------------------------------ 
echo
fi

if test "x$ac_have_expat" = "xno"; then
echo ------------------------------------------------------------------ 
echo "The expat library has not been found.                            "
echo "It might be the case that either libexpat is not installed on    "
echo "your system, or it is actually installed, but configure could not"
echo "find it. See configure options --with-expat-{inc,lib}dir to help "
echo "configure finding expat if it is installed in non-standard paths."
echo "**  If you run 'make' now, NuGaT would still build correctly   **"
echo "**  but the functionality to load saved traces from a file     **"
echo "**  will not be available.                                     **"
echo ------------------------------------------------------------------ 
echo
fi

if test "$opt_static_link" = yes; then
echo ------------------------------------------------------------------ 
echo "As you requested, all executables will be statically linked."
echo ------------------------------------------------------------------ 
echo
fi
