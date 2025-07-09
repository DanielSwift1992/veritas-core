FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y python3 python3-pip g++ curl git

COPY . /delta
WORKDIR /delta

# Install Python deps if requirements file exists
RUN if [ -f artifact/code/requirements.txt ]; then \
        pip3 install -r artifact/code/requirements.txt; \
    fi

CMD ["veritas", "check", "--quiet", "--stats"] 