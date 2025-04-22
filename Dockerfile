FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# Install QEMU build dependencies
RUN apt-get update && apt-get install -y \
    git build-essential ninja-build \
    python3 python3-pip python3-venv \
    libglib2.0-dev libpixman-1-dev zlib1g-dev \
    libfdt-dev libffi-dev libssl-dev libcap-ng-dev \
    libattr1-dev libncurses5-dev pkg-config \
    flex bison curl unzip ca-certificates \
    cmake \
    clang lld llvm-dev llvm \
    && rm -rf /var/lib/apt/lists/*

# Install Meson
RUN pip3 install meson==1.2.3

# Create build directory
WORKDIR /opt

# Clone SymFit  (or replace with COPY if local)

RUN git clone https://github.com/enlighten5/symfit-kernel.git /opt/symfit
WORKDIR /opt/symfit

# Configure for softmmu + linux-user
RUN ./configure \
    --target-list=x86_64-softmmu,x86_64-linux-user \
    --enable-linux-user \
    --disable-werror

# Build QEMU
RUN make -j$(nproc)

# Set default command
CMD ["bash"]
