FROM ubuntu:20.04

RUN export DEBIAN_FRONTEND=noninteractive && \
    apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y \
        make \
        texlive-latex-base \
        texlive-latex-recommended \
        texlive-latex-extra \
        texlive-plain-generic \
        texlive-fonts-extra \
        texlive-lang-french \
        texlive-luatex \
        python3-pygments \
        librsvg2-bin && \
    apt-get clean autoclean && \
    apt-get autoremove -y && \
    rm -rf /var/lib/{apt,dpkg,cache,log}/