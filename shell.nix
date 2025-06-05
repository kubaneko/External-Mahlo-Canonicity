{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [
     texlive.combined.scheme-full
     python312Packages.pygments
  ];
}
