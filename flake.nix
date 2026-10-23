{
  # nixConfig.extra-substituters = [
  #   "https://mikan.cachix.org"
  #   "https://1lab.cachix.org"
  # ];
  # nixConfig.extra-trusted-public-keys = [
  #   "mikan.cachix.org-1:l1i58iAKFlQr1VcWPaYXExVYoVVPx8vXs+jfEttRFhA="
  #   "1lab.cachix.org-1:eYjd9F9RfibulS4OSFBYeaTMxWojPYLyMqgJHDvG1fs="
  # ];

  inputs = {
    # nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    nixpkgs.url = "github:ncfavier/nixpkgs/agda-parallel";
    mikan.url = "git+https://codeberg.org/1lab/mikan";
    # mikan.url = "git+https://codeberg.org/1lab/mikan?rev=2f7dce157928563a52632be23765ae28776c5afe";
    # agda-stdlib = {
    #   url = "git+https://codeberg.org/amyliao/agda-stdlib";
    #   flake = false;
    # };
    cubical = {
      url = "git+https://codeberg.org/1lab/agda-cubical";
      flake = false;
    };
    the1lab = {
      url = "github:the1lab/1lab";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
      overlays = [
        inputs.mikan.overlays.default
        (final: prev: {
          haskell = prev.haskell // {
            packageOverrides = final.lib.composeExtensions prev.haskell.packageOverrides
              (hfinal: hprev: {
                # Mikan = inputs.mikan.packages.${system}.default;
                Agda = hfinal.Mikan;
              });
          };
          agdaPackages = prev.agdaPackages.overrideScope (aself: asuper: {
            # standard-library = asuper.standard-library.overrideAttrs {
            #   version = "unstable-${inputs.agda-stdlib.shortRev}";
            #   src = inputs.agda-stdlib;
            #   postPatch = ''
            #     rm -rf Algebra
            #   '';
            # };
            _1lab = asuper._1lab.overrideAttrs {
              version = "unstable-${inputs.the1lab.shortRev}";
              src = inputs.the1lab;
            };
            cubical = asuper.cubical.overrideAttrs {
              version = "unstable-${inputs.cubical.shortRev}";
              src = inputs.cubical;
            };
          });
        })
      ];
    };
    inherit (pkgs) lib;

    agdaLibs = libs: [
      # libs.standard-library
      libs.cubical
      libs._1lab
    ];
    agda = pkgs.agdaPackages.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.agdaPackages.mkLibraryFile agdaLibs;

    texlive = pkgs.texliveSmall.withPackages (tpkgs: with tpkgs; [
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd pgfplots
      mathpazo
      varwidth xkeyval standalone
    ]);

    deps = [
      pkgs.pandoc-katex
      texlive
      pkgs.poppler-utils
    ];

    PANDOC_KATEX_CONFIG_FILE = pkgs.writeText "katex-config.toml" ''
      trust = true
      throw_on_error = true

      [macros]
      "\\bN" = "\\mathbb{N}"
      "\\bZ" = "\\mathbb{Z}"
    '';

    hpkgs = pkgs.haskellPackages;
    shakefile = hpkgs.callCabal2nix "agda-stuff-shake" ./shake {};
  in {
    devShells.${system} = {
      default = self.packages.${system}.default.overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs or [] ++ [ agda ];
        Mikan = hpkgs.Mikan;
      });

      shakefile = hpkgs.shellFor {
        packages = _: [ shakefile ];
        nativeBuildInputs = deps ++ [
          pkgs.haskell-language-server
        ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
      };
    };

    packages.${system} = {
      default = pkgs.stdenv.mkDerivation {
        name = "agda-stuff";
        src = self;
        nativeBuildInputs = deps ++ [ shakefile ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
        LC_ALL = "C.UTF-8";
        buildPhase = ''
          agda-stuff-shake
          mv _build/site "$out"
        '';
      };

      inherit shakefile;
    };
  };
}
