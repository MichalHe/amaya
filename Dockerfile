FROM debian
RUN apt update
RUN apt install -y gcc g++ cmake make git python3 python3-pip python3-dev libgmp-dev libhwloc-dev pkg-config

RUN git clone https://github.com/trolando/sylvan.git sylvan
RUN mkdir -p sylvan/build
WORKDIR sylvan
RUN git checkout v1.5.0
RUN sed -i 's/-Werror//g' CMakeLists.txt
WORKDIR build
RUN cmake ..
RUN make -j`nproc`
RUN make install
RUN ldconfig

WORKDIR /
COPY . /amaya
WORKDIR amaya
RUN pip3 install -r requirements.txt --break-system-packages
RUN pip3 install cython setuptools --break-system-packages

# The MTBDD backend (mtbdd-backend/) is compiled into a Cython extension
# (libamaya) and dropped into amaya/, replacing the old ctypes-based
# amaya-mtbdd.so built from a separate cloned repo. CPATH/LIBRARY_PATH point
# the extension build at the sylvan headers/lib just installed above, since
# mtbdd-backend/wrapper/compile_wrapper.py's own search paths are dev-machine
# specific.
ENV CPATH="/usr/local/include"
ENV LIBRARY_PATH="/usr/local/lib"
ENV LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:/usr/local/lib"
RUN make -C mtbdd-backend libamaya PYTHON=python3
