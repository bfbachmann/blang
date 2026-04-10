FROM rust:latest
WORKDIR /usr/src/blang

ARG LLVM_VERSION=21

# Set envvars necessary for building with LLVM
ENV LLVM_SYS_211_PREFIX=/usr/lib/llvm-$LLVM_VERSION

# Install LLVM and other dependencies
RUN apt-get update \
    && apt-get install -y lsb-release \
    && wget https://apt.llvm.org/llvm.sh  \
    && chmod +x llvm.sh \
    && ./llvm.sh $LLVM_VERSION all

# Copy the compiler source code and libraries to the container
COPY Cargo.lock Cargo.toml ./
COPY src ./src
COPY std ./std

# Build the Blang compiler
RUN cargo install --path . --locked
