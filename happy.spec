%define name    happy
%define version 1.14
%define release 1

Name:           %{name}
Version:        %{version}
Release:        %{release}
License:        BSD-like
Group:          Development/Languages/Haskell
URL:            http://haskell.org/happy/
Source:         http://haskell.org/happy/dist/%{version}/happy-%{version}-src.tar.gz
Packager:       Sven Panne <sven.panne@aedion.de>
BuildRoot:      %{_tmppath}/%{name}-%{version}-build
Prefix:         %{_prefix}
BuildRequires:  ghc, docbk31
Summary:        The LALR(1) Parser Generator for Haskell

%description
Happy is a parser generator system for Haskell, similar to the tool
`yacc' for C. Like `yacc', it takes a file containing an annotated BNF
specification of a grammar and produces a Haskell module containing a
parser for the grammar.

Happy is flexible: you can have several Happy parsers in the same
program, and several entry points to a single grammar. Happy can work
in conjunction with a lexical analyser supplied by the user (either
hand-written or generated by another program), or it can parse a
stream of characters directly (but this isn't practical in most
cases).

Authors:
--------
    Simon Marlow <simonmar@microsoft.com>
    Andy Gill <andy@galconn.com>

%prep
%setup -n happy-%{version}

%build
test -f configure || autoreconf
./configure --prefix=%{prefix}
make
( cd happy/doc ; make dvi ps html ; gzip -f -9 *.dvi *.ps )

%install
make prefix=${RPM_BUILD_ROOT}%{prefix} install

%clean
rm -rf ${RPM_BUILD_ROOT}

%files
%defattr(-,root,root)
%doc happy/ANNOUNCE
%doc happy/CHANGES
%doc happy/LICENSE
%doc happy/README
%doc happy/TODO
%doc happy/doc/happy
%doc happy/doc/happy.dvi.gz
%doc happy/doc/happy.ps.gz
%doc happy/examples
%{prefix}/bin/happy
%{prefix}/bin/happy-%{version}
%{prefix}/lib/happy-%{version}
