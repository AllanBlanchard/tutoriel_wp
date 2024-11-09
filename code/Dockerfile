FROM debian:trixie

RUN apt-get update && apt-get install -y \
  bash \
  build-essential \
  bzip2 \
  ca-certificates \
  cvc5 \
  curl \
  diffutils \
  gcc \
  git \
  make \
  opam \
  patch \
  rsync \
  tar \
  unzip \
  wget \
  which

RUN opam init -c 4.14.2 --disable-sandboxing

RUN opam install --confirm-level=unsafe-yes \
  dune \
  dune-configurator \
  dune-site \
  alt-ergo \
  coq \
  menhir \
  ocamlgraph \
  unionFind \
  why3 \
  why3-coq \
  yaml \
  yojson \
  zarith \
  ppx_deriving \
  ppx_deriving_yojson \
  ppx_deriving_yaml

ENV HOME="/root"

ENV OPAM_SWITCH_PREFIX="$HOME/.opam/4.14.2"
ENV CAML_LD_LIBRARY_PATH="$OPAM_SWITCH_PREFIX/lib/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH="$OPAM_SWITCH_PREFIX/lib/toplevel"
ENV PATH="$OPAM_SWITCH_PREFIX/bin:$PATH"

RUN wget https://git.frama-c.com/pub/frama-c/-/archive/master/frama-c-master.tar.gz
RUN tar xzf frama-c-master.tar.gz
RUN make PREFIX=$OPAM_SWITCH_PREFIX RELEASE=yes -C frama-c-master install

RUN why3 config detect
