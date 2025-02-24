#!/bin/bash
sudo apt-get update && sudo apt-get upgrade -y
sudo apt-get install -y --no-install-recommends \
    libgflags-dev \
    libboost-all-dev \ 
    wget \
    curl \
    git \
    vim \
    nano \
    gcc \
    g++ \
    gdb \
    make \
    build-essential \
    cmake \
    pkg-config \
    python3 \
    python3-pip \
    python3-venv \
    nodejs \
    npm \
    openjdk-11-jdk \
    ruby-full \
    perl \
    php-cli \
    php-mbstring \
    php-xml \
    php-curl \
    libssl-dev \
    zlib1g-dev \
    libbz2-dev \
    libreadline-dev \
    libsqlite3-dev \
    libffi-dev \
    libncurses5-dev \
    libncursesw5-dev \
    liblzma-dev \
    xz-utils \
    tk-dev \
    libxml2-dev \
    libxmlsec1-dev \
    uuid-dev \
    zip \
    unzip \
    iputils-ping \
    net-tools \
    dnsutils \
    ssh \
    m4 \
    libgmp-dev \
    libedit-dev \
    flex \
    bison \
    nasm \
    man \
    neofetch \
    llvm \
    lldb \
    clang \
    gcc-multilib \
    libgtest-dev \
    htop \
    ninja-build \
    wget \
    net-tools \
    curl \
    llvm-dev \
    libclang-dev \
    clang \
    m4 \
    x11-apps \
    software-properties-common \
    time

# install kali-linux-default
# sudo apt install -y kali-linux-default

# install ubuntu-restricted-extras
# sudo apt-get install -y ubuntu-restricted-extras

# install tasksel
# sudo apt-get install tasksel
# sudo tasksel

# install rust
# curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# other optional install
# sudo apt-get install -y fzf htop

echo "install done!"
