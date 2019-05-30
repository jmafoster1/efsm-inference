import Dependencies._
import sys.process._
import java.io.File;

val cleanSalfiles = taskKey[Int]("Deletes everything from the ./salfiles folder")
val cleanDotfiles = taskKey[Int]("Deletes everything from the ./dotfiles folder")
val mkdirs = taskKey[Unit]("Creates the ./salfiles and ./dotfiles directories for the program to put stuff in as it runs")
val setEnv = taskKey[Int]("Adds the necessary SAL header files to the environment variable SALCONTEXTPATH")

ThisBuild / scalaVersion     := "2.12.8"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "com.example"
ThisBuild / organizationName := "example"

def cleanDirectory(dirName: String):Int = {
  val file = new File(dirName)
  if (file.isDirectory) {
    for (f <- file.listFiles) {
      if (!f.delete) {
        return 1
      }
    }
  }
  return 0
}

def mkdir(name: String) = {
  val dir = new File(name)
  if (!dir.isDirectory || !dir.exists) {
    dir.mkdir();
  }
}

lazy val root = (project in file("."))
  .settings(
    name := "inference-tool",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "net.liftweb" %% "lift-json" % "3.3.0",
    cleanSalfiles := {
      cleanDirectory("salfiles")
    },
    cleanDotfiles := {
      cleanDirectory("dotfiles")
    },
    clean := clean.dependsOn(cleanSalfiles, cleanDotfiles).value,
    mkdirs := {
      mkdir("salfiles")
      mkdir("dotfiles")
    },
    (run in Compile) := (run in Compile).dependsOn(mkdirs).evaluated,
    setEnv := {
      println(System.getProperty("user.dir"));
      System.setProperty("SALCONTEXTPATH", s"${System.getProperty("user.dir")}/lib/:.")
      // s"export SALCONTEXTPATH=${System.getProperty("user.dir")}/lib/:.".!;
      0
    }

  )

// Uncomment the following for publishing to Sonatype.
// See https://www.scala-sbt.org/1.x/docs/Using-Sonatype.html for more detail.

// ThisBuild / description := "Some descripiton about your project."
// ThisBuild / licenses    := List("Apache 2" -> new URL("http://www.apache.org/licenses/LICENSE-2.0.txt"))
// ThisBuild / homepage    := Some(url("https://github.com/example/project"))
// ThisBuild / scmInfo := Some(
//   ScmInfo(
//     url("https://github.com/your-account/your-project"),
//     "scm:git@github.com:your-account/your-project.git"
//   )
// )
// ThisBuild / developers := List(
//   Developer(
//     id    = "Your identifier",
//     name  = "Your Name",
//     email = "your@email",
//     url   = url("http://your.url")
//   )
// )
// ThisBuild / pomIncludeRepository := { _ => false }
// ThisBuild / publishTo := {
//   val nexus = "https://oss.sonatype.org/"
//   if (isSnapshot.value) Some("snapshots" at nexus + "content/repositories/snapshots")
//   else Some("releases" at nexus + "service/local/staging/deploy/maven2")
// }
// ThisBuild / publishMavenStyle := true
