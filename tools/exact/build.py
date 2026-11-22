"""Compile the Java ground-truth tools (tools/exact/java -> tools/exact/classes). Run from anywhere."""
import glob, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
JAR = os.path.join(ROOT, "reference", "bin", "org.alloytools.alloy.dist.jar")
srcs = glob.glob(os.path.join(HERE, "java", "**", "*.java"), recursive=True)
os.makedirs(os.path.join(HERE, "classes"), exist_ok=True)
r = subprocess.run(["javac", "-nowarn", "-cp", JAR, "-d", os.path.join(HERE, "classes")] + srcs)
sys.exit(r.returncode)
