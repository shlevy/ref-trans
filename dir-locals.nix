let pkgs = import <nixpkgs> {};
in pkgs.nixBufferBuilders.withPackages [ pkgs.coq_8_7 ]
