FROM ubuntu:latest

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y \
      curl wget vim-tiny git unzip \
      build-essential sloccount graphviz python3 python3-venv time \
      clang libc++-dev libc++abi-dev libdb5.3-stl-dev libdb-dev libdb++-dev

RUN python3 -m venv /root/venv3-veribetrfs && \
    . /root/venv3-veribetrfs/bin/activate && \
    pip3 install toposort numpy matplotlib

RUN curl -O https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y apt-transport-https && \
    apt-get update && \
    apt-get install -y dotnet-sdk-5.0
