% !TEX root = arthur-book.cls
% !TEX encoding = UTF-8 Unicode
% arthur-book.cls
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{arthur-book}[2025/09/03 Arthur's constructive book class]

% ---------- Options ----------
\newif\ifarthur@tight
\newif\ifarthur@print
\newif\ifarthur@widenotes
\DeclareOption{tight}{\arthur@tighttrue\arthur@printfalse\arthur@widenotesfalse}
\DeclareOption{print}{\arthur@tightfalse\arthur@printtrue\arthur@widenotesfalse}
\DeclareOption{wide-notes}{\arthur@tightfalse\arthur@printfalse\arthur@widenotestrue}
\DeclareOption*{} % ignore unknown
\ExecuteOptions{tight} % default
\ProcessOptions\relax

% ---------- Base class ----------
% Tufte-style monograph: one-sided layout so the wide margin column is
% always on the right and the page-number box always at top-left.
\LoadClass[11pt,openany,oneside]{book}

% ---------- Required packages ----------
\RequirePackage{etoolbox}
\RequirePackage{geometry}
\RequirePackage{fancyhdr}
\RequirePackage{titlesec}
\RequirePackage{titletoc}
\RequirePackage{microtype}
\RequirePackage{ifthen}
\RequirePackage{calc}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{mathtools}
\RequirePackage{hyperref}
\hypersetup{hidelinks}

% ---------- Geometry presets ----------
% tight  : ~36pt side margins, compact top/bottom
% print  : comfortable book-ish margins
% wide-notes : Tufte-like outer margin for sidenotes
\ifarthur@tight
  \geometry{
    paperwidth=8.5in,paperheight=11in,
    inner=36pt, outer=36pt,
    top=36pt, bottom=48pt,
    headheight=18pt, headsep=18pt, footskip=18pt,
    includehead, includefoot
  }
\fi
\ifarthur@print
  \geometry{
    paperwidth=8.5in,paperheight=11in,
    inner=28mm, outer=32mm,
    top=24mm, bottom=28mm,
    headheight=18pt, headsep=18pt, footskip=20pt,
    includehead, includefoot
  }
\fi
\ifarthur@widenotes
  % Tufte-like letterpaper layout: text column on the left, wide note
  % column on the right, on every page (one-sided book class).
  \geometry{
    letterpaper,
    left=1in,
    top=1in,
    textwidth=26pc,
    marginparsep=2pc,
    marginparwidth=12pc,
    textheight=44\baselineskip,
    headheight=\baselineskip,
    headsep=2\baselineskip,
    footskip=2\baselineskip
  }
\fi

% ---------- Depth of numbering (Arthur wants details!) ----------
\setcounter{secnumdepth}{6}
\setcounter{tocdepth}{6}

% ---------- Remove forced page clears around \chapter ----------
\makeatletter
\pretocmd{\chapter}{\@afterindentfalse}{}{}
\patchcmd{\chapter}{\if@openright\cleardoublepage\else\clearpage\fi}{}{}{}
\patchcmd{\@chapter}{\clearpage}{}{}{}
\patchcmd{\@schapter}{\clearpage}{}{}{}
\makeatother

% ---------- Chapter/Section formatting ----------
\titleformat{\chapter}[hang]
  {\huge\bfseries}
  {\thechapter\;\;\rule[-0.3ex]{.5pt}{1.25em}}
  {1em}
  {\Huge}
  [\vspace{0.5ex}\rule{\textwidth}{0.5pt}\vspace{0.75ex}]
\titlespacing*{\chapter}{0pt}{1.2ex plus .3ex}{1.0ex}

\titleformat{\section}[hang]
  {\Large\bfseries}
  {\thesection}{0.6em}{}
\titlespacing*{\section}{0pt}{1.0ex plus .2ex}{0.5ex}

\titleformat{\subsection}[hang]
  {\large\bfseries}
  {\thesubsection}{0.5em}{}
\titlespacing*{\subsection}{0pt}{0.8ex plus .2ex}{0.4ex}

\titleformat{\subsubsection}[runin]
  {\normalsize\bfseries}
  {\thesubsubsection}{0.5em}{}[.]

% ---------- TOC: compact dotted leaders ----------
\contentsmargin{2em}
\dottedcontents{chapter}[0em]{}{\dimexpr1.5em+1.5ex}{0.8em}
\dottedcontents{section}[1.6em]{}{\dimexpr2.3em+1.5ex}{0.8em}
\dottedcontents{subsection}[3.2em]{}{\dimexpr3.1em+1.5ex}{0.8em}
\dottedcontents{subsubsection}[4.8em]{}{\dimexpr3.9em+1.5ex}{0.8em}
\dottedcontents{subsubsubsection}[6.4em]{}{\dimexpr4.7em+1.5ex}{0.8em}

% ---------- Header path: chapter --> section --> subsection ----------
% We'll track current chapter/section/subsection titles and compose a path.
\makeatletter
\newcommand*\arthur@chapname{}
\newcommand*\arthur@secname{}
\newcommand*\arthur@subsecname{}
\newcommand*\arthur@subsubsecname{}
\newcommand*\arthur@subsubsubsecname{}
\renewcommand{\chaptermark}[1]{%
  \gdef\arthur@chapname{#1}%
  \gdef\arthur@secname{}%
  \gdef\arthur@subsecname{}%
  \gdef\arthur@subsubsecname{}%
  \gdef\arthur@subsubsubsecname{}%
}
\renewcommand{\sectionmark}[1]{%
  \gdef\arthur@secname{#1}%
  \gdef\arthur@subsecname{}%
  \gdef\arthur@subsubsecname{}%
  \gdef\arthur@subsubsubsecname{}%
}
\renewcommand{\subsectionmark}[1]{%
  \gdef\arthur@subsecname{#1}%
  \gdef\arthur@subsubsecname{}%
  \gdef\arthur@subsubsubsecname{}%
}
\renewcommand{\subsubsectionmark}[1]{%
  \gdef\arthur@subsubsecname{#1}%
  \gdef\arthur@subsubsubsecname{}%
}
\newcommand{\subsubsubsectionmark}[1]{\gdef\arthur@subsubsubsecname{#1}}
\newcommand{\arthur@path}{%
  \ifx\arthur@chapname\@empty\else \arthur@chapname\fi
  \ifx\arthur@secname\@empty\else \,{\footnotesize$\rightarrow$}\, \arthur@secname\fi
  \ifx\arthur@subsecname\@empty\else \,{\footnotesize$\rightarrow$}\, \arthur@subsecname\fi
  \ifx\arthur@subsubsecname\@empty\else \,{\footnotesize$\rightarrow$}\, \arthur@subsubsecname\fi
  \ifx\arthur@subsubsubsecname\@empty\else \,{\footnotesize$\rightarrow$}\, \arthur@subsubsubsecname\fi
}
\makeatother

% ---------- Page number box helper ----------
\makeatletter
\newcommand{\arthur@pagebox}{%
  \begingroup
  \setlength\fboxsep{2pt}%
  \setlength\fboxrule{0.4pt}%
  \fbox{\normalsize\thepage}%
  \endgroup
}

% ---------- Header rule (paper-edge-aligned, butted against the page box) ----------
% One-sided layout: the page-box is always at top-left and the rule runs
% from the box's right edge to the right paper edge.  Vertical position is
% the page-box's baseline (`\rule[0pt]`), so the rule touches the bottom
% of the printed page number.
\newlength{\arthur@pageboxwidth}

\newcommand{\arthur@headrule}{%
  \settowidth{\arthur@pageboxwidth}{\arthur@pagebox}%
  \makebox[0pt][l]{%
    \hspace*{\dimexpr -\oddsidemargin-1in+2pt+\arthur@pageboxwidth}%
    \rule[0pt]{\dimexpr \paperwidth-4pt-\arthur@pageboxwidth}{0.4pt}%
  }%
}

\newcommand{\arthur@headerlabel}{\raisebox{0.45ex}{\textsc{\small \arthur@path}}}

% ---------- Headers/footers ----------
\pagestyle{fancy}
\fancyhf{} % clear

% Single header style (one-sided): page box at far left of paper, then the
% running label, then the rule running from the box's right edge to the
% right paper edge.
\fancyhead[L]{%
  \arthur@headrule
  \makebox[0pt][l]{\hspace*{\dimexpr -\oddsidemargin-1in+2pt}\arthur@pagebox}%
  \quad\arthur@headerlabel
}

% No footer page number: the boxed top-left label is the single source.
\fancyfoot[C]{}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}

% Chapter pages (which use \thispagestyle{plain}) and front-matter pages
% otherwise default to plain.  Override the plain style so it also has
% no footer page number; the boxed top-corner label still renders via
% the fancy style on subsequent pages, but on the chapter's first page
% the page is intentionally clean.
\fancypagestyle{plain}{%
  \fancyhf{}%
  \renewcommand{\headrulewidth}{0pt}%
  \renewcommand{\footrulewidth}{0pt}%
}
\makeatother

% ---------- Title page ----------
% In wide-notes mode the text column lives on the left half of the paper.
% The default book-class \maketitle centers within the text column, which
% looks off-center on the page.  Replace with an explicit paper-centered
% title block that spans the full paper width.
\makeatletter
\ifarthur@widenotes
  \renewcommand{\maketitle}{%
    \thispagestyle{empty}%
    \null\vfil
    \vskip 60\p@
    \makebox[0pt][l]{%
      % Jump from text-column origin to paper's left edge:
      \hspace*{\dimexpr -\oddsidemargin-1in\relax}%
      \hbox to \paperwidth{%
        \hss
        \begin{minipage}{0.72\paperwidth}\centering
          {\LARGE\bfseries \@title \par}%
          \vskip 2.5em
          {\large \@author \par}%
          \vskip 1.5em
          {\large \@date \par}%
        \end{minipage}%
        \hss
      }%
    }%
    \vfil\null
    \clearpage
  }%
  % TOC keeps the original (text-column) geometry; the dotted-leader layout
  % already reads cleanly within the text column even though the page itself
  % is asymmetric.
\fi
\makeatother

% ---------- Arthur modules ----------
\RequirePackage{tex/arthur-symbols}
\RequirePackage{tex/arthur-math}
\RequirePackage{tex/arthur-notation}
\RequirePackage{tex/arthur-margin-citations}
\RequirePackage{tex/arthur-figures}
\RequirePackage{tex/arthur-tikz}

% ---------- End class ----------
