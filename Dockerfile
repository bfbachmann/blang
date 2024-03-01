FROM rust:latest as builder
WORKDIR /usr/src/blang

# Install LLVM and other dependencies
RUN apt-get update && \
    apt-get install -y llvm-16 libpolly-16-dev

# Set envvars necessary for building with LLVM
ENV LLVM_SYS_160_PREFIX=/usr/lib/llvm-16

# Copy the compiler source code and libraries to the container
COPY Cargo.lock Cargo.toml ./
COPY src ./src
COPY std ./std

# Build the Blang compiler
RUN cargo install --path . --locked
