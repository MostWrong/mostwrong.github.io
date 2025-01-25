FROM ubuntu:latest

WORKDIR /LeanProject

COPY . .

RUN apt-get update && apt-get install -y \
    curl git cmake && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME="/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y

EXPOSE 3000

RUN lake build

CMD ["lake", "exe", "httpserver", "--port", "3000", "--bind", "0.0.0.0"]
