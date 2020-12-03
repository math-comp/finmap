#!/usr/bin/env bash
set -e
# set -x

if [ -z $1 ] || [ -z $2 ] || [ -z $3 ] || [ -z $4 ] || \
   [ $1 == "--help" ] || [ $1 == "-h" ]
then cat <<EOF
usage : packager GITHUBUSER PROJECT VERSION URL"
- GITHUBUSER is your github username, you must have a fork of
    coq/opam-coq-archive under
    https://github.com/$GITHUBUSER/opam-coq-archive
    for this command to work
- VERSION is the opam version number of the package to create
- PROJECT is a name of the project, without space, it is used
    solely for generating the name of the branch and PR
- URL is the url of the archive associated with the version to
    release
EOF
     exit 0
else
GITHUBUSER=$1
PROJECT=$2
VERSION=$3
URL=$4
fi

COA=$(mktemp -d) # stands for Coq Opam Archive
git clone --depth=10 git@github.com:coq/opam-coq-archive $COA -o upstream
git -C $COA remote add\
  origin git@github.com:$GITHUBUSER/opam-coq-archive
BRANCH=$PROJECT.$VERSION
git -C $COA checkout -b $BRANCH
PKGS=$COA/released/packages

ARCHIVE=$(mktemp)
curl -L $URL -o $ARCHIVE
SUM=$(sha256sum $ARCHIVE | cut -d " " -f 1)

for opam in *.opam
do B=$(basename $opam .opam)
   P=$PKGS/$B/$B.$VERSION
   mkdir -p $P
   sed "/^version:.*/d" $opam > $P/opam
   echo "" >> $P/opam
   echo "url {" >> $P/opam
   echo "  src: \"$URL\"" >> $P/opam
   echo "  checksum: \"sha256=$SUM\"" >> $P/opam
   echo "}" >> $P/opam

   opam lint --check-upstream $P/opam

   git -C $COA add $P/opam
done
git -C $COA commit -m "Release $PROJECT $VERSION"
git -C $COA push origin -f $BRANCH

echo "**********************************************************************"
echo "Create a pull request by visiting"
echo "https://github.com/$GITHUBUSER/opam-coq-archive/pull/new/$BRANCH"
echo "**********************************************************************"
