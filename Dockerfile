FROM debian 
RUN apt update
RUN apt install -y gcc cmake make git python3 python3-pip libgmp-dev libhwloc-dev pkg-config

RUN git clone https://github.com/trolando/sylvan.git sylvan
RUN mkdir -p sylvan/build
WORKDIR sylvan
RUN git checkout v1.5.0
RUN sed -i 's/-Werror//g' CMakeLists.txt
WORKDIR build
RUN cmake ..
RUN make -j`nproc`
RUN make install

WORKDIR /
RUN git clone https://github.com/MichalHe/amaya-mtbdd.git amaya-mtbdd
WORKDIR amaya-mtbdd
RUN make -j`nproc` shared-lib

WORKDIR /
COPY . /amaya
WORKDIR amaya
RUN cp /amaya-mtbdd/build/amaya-mtbdd.so /amaya/amaya/
RUN pip3 install -r requirements.txt --break-system-packages
ENV LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:/usr/local/lib/"
ENTRYPOINT ["./run-amaya.py", "--fast", "-O", "all", "get-sat"]
