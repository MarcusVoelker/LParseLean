{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-25.11";
  };

  outputs = inputs:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: inputs.nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = import inputs.nixpkgs { inherit system; };
      });
    in
    {
      devShells = forEachSupportedSystem ({ pkgs }:
      let
        lean4new = pkgs.lean4.overrideAttrs (finalAttrs: prevAttrs: {
          version = "nightly-2026-01-07";
          src = pkgs.fetchzip {
            url = "https://github.com/leanprover/lean4-nightly/archive/refs/tags/nightly-2026-01-07.zip";
            hash = "sha256-234hzZibVR/+bZoRsAu4FFhyQ9KYr6iyeNOb1hssb7s=";
          };
          postPatch =
             let
               pattern = "\${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc";
             in
             ''
               substituteInPlace src/CMakeLists.txt \
                 --replace-fail 'set(GIT_SHA1 "")' 'set(GIT_SHA1 "nightly-2026-01-07")'

               # Remove tests that fails in sandbox.
               # It expects `sourceRoot` to be a git repository.
               rm -rf src/lake/examples/git/
             ''
             + (inputs.nixpkgs.lib.optionalString true ''
               substituteInPlace CMakeLists.txt \
                 --replace-fail 'MIMALLOC-SRC' '${finalAttrs.mimalloc-src}'
               for file in stage0/src/CMakeLists.txt stage0/src/runtime/CMakeLists.txt src/CMakeLists.txt src/runtime/CMakeLists.txt; do
                 substituteInPlace "$file" \
                   --replace-fail '${pattern}' '${finalAttrs.mimalloc-src}'
               done
             '');
        });
      in
      {
        default = pkgs.mkShell {
          name = "lean";
          packages = with pkgs; [
            lean4new
          ];
        };
      });
    };
}
