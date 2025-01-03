FROM rust:latest as builder
WORKDIR /usr/src/blang

# Install LLVM and other dependencies
RUN apt-get update && \
    apt-get install -y llvm-18 libpolly-18-dev

# Set envvars necessary for building with LLVM
ENV LLVM_SYS_180_PREFIX=/usr/lib/llvm-18

# Copy the compiler source code and libraries to the container
COPY Cargo.lock Cargo.toml ./
COPY src ./src
COPY std ./std

# Build the Blang compiler
RUN cargo install --path . --locked
