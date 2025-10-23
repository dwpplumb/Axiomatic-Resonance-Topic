# folders
$ROOT = "C:\development\art_pv_np"
$OUT  = Join-Path $ROOT "bench"
New-Item -ItemType Directory -Force -Path $OUT | Out-Null

# params (adapt to taste)
$N = 150
$P = 0.5
$K_CLIQUE = 18        # <-- was --k before; must be --k_clique
$D = 128
$K_PROJ = 32          # <-- projection size; use --k_proj
$TRP = 1000; $TRN = 1000
$VAP = 500;  $VAN = 500
$TEP = 2000; $TEN = 2000
$SEED = 1

# run
python "$ROOT\graphbench.py" `
  --problem planted_clique `
  --n $N --p $P `
  --k_clique $K_CLIQUE `
  --d $D --k_proj $K_PROJ `
  --n_train_yes $TRP --n_train_no $TRN `
  --n_val_yes   $VAP --n_val_no   $VAN `
  --n_test_yes  $TEP --n_test_no  $TEN `
  --seed $SEED `
  --out (Join-Path $OUT "pc_${N}_k${K_CLIQUE}_seed${SEED}.json")
