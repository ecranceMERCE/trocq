FROM coqorg/coq:8.20.1
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y coq-lsp coq-elpi
RUN mkdir /home/coq/trocq
# ADD https://github.com/rocq-community/trocq.git /home/coq/trocq
ADD . /home/coq/trocq
USER root
RUN chown -R coq:coq trocq
USER coq
RUN rm -rf trocq/.git
RUN opam pin trocq -yn
RUN opam install -y --deps-only coq-trocq-dev
