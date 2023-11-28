BINDING = """
let loaded = false
onmessage = async ev => {
    if (!loaded) {
        await wasm_bindgen("./osmarkscalculator.wasm")
        loaded = true
    }
    var [fn, ...args] = ev.data
    let init = false
    if (fn === "deinit") {
        wasm_bindgen.deinit_context()
        init = false
    } else if (fn === "run") {
        const start = performance.now()
        try {
            if (!init) {
                wasm_bindgen.init_context()
                wasm_bindgen.load_defaults()
                init = true;
            }
            postMessage(["ok", wasm_bindgen.run_program(args[0]), performance.now() - start])
        } catch(e) {
            postMessage(["error", e.toString(), performance.now() - start])
        }
    }
}
"""
HEADER = """
---
title: osmarkscalculator
description: Unholy horrors moved from the depths of my projects directory to your browser. Theoretically, this is a calculator. Good luck using it.
---
""".strip()
import subprocess, rjsmin, os, shutil
subprocess.run(["wasm-pack", "build", "--target=no-modules"])
minified = rjsmin.jsmin(open("pkg/osmarkscalculator.js", "r").read() + BINDING)
os.makedirs("dist", exist_ok=True)
subprocess.run(["wasm-opt", "-Oz", "pkg/osmarkscalculator_bg.wasm", "-o", "dist/osmarkscalculator.wasm"])
open("dist/osmarkscalculator.js", "w").write(minified)
with open("index.html") as f:
    g = HEADER + f.read().replace("""<meta charset="UTF-8">""", "")
with open("dist/index.html", "w") as h:
    h.write(g)
shutil.copytree("dist/.", "../website/experiments/osmarkscalculator", dirs_exist_ok=True)