{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/650a295621b27c4ebe0fa64a63fd25323e64deb3.tar.gz";
  sha256 = "0rxjkfiq53ibz0rzggvnp341b6kgzgfr9x6q07m2my7ijlirs2da";
}),
coq-version ? "8.9",
mc ? fetchGit {url = "/home/ccohen/git/math-comp/experiment/order/"; ref = "order";},
print-env ? false
}:
let
  config.packageOverrides = pkgs:
    with pkgs; rec {
      coqPackages =
        let coqPackages = (with pkgs; {
              "8.7" = coqPackages_8_7;
              "8.8" = coqPackages_8_8;
              "8.9" = coqPackages_8_9;
              "8.10" = coqPackages_8_10;
          }."${coq-version}");
        in
        coqPackages.overrideScope' (self: super: {
          mathcompPkgs = if builtins.isString mc then (super.mathcompGen mc)
                         else super.mathcomp.mathcompGen (o: {
                            version = "dev";
                            name = "coq${self.coq.coq-version}-mathcomp-dev";
                            src = mc;
             });
           mathcomp = self.mathcompPkgs.all;
           mathcomp-ssreflect = self.mathcompPkgs.ssreflect;
       });
       coq = coqPackages.coq;
    };
in
with import nixpkgs {inherit config;};
let
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages; [mathcomp-ssreflect])
                ++ lib.optional withEmacs pgEmacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}
