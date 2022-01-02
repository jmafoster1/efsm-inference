import Dependencies._
import sys.process._
import java.io.File;

val cleanDotfiles = taskKey[Int]("Deletes everything from the ./dotfiles folder")
val mkdirs = taskKey[Unit]("Creates the ./dotfiles directories for the program to put stuff in as it runs")
val buildDOT = taskKey[Unit]("Builds the dotfiles")

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

assemblyMergeStrategy in assembly := {
 case PathList("META-INF", xs @ _*) => MergeStrategy.discard
 case x => MergeStrategy.first
}

mainClass in assembly := Some("FrontEnd")

def mkdir(name: String) = {
  val dir = new File(name)
  if (!dir.isDirectory || !dir.exists) {
    dir.mkdir();
  }
}

def getListOfFiles(dir: File, extensions: List[String]): List[File] = {
    dir.listFiles.filter(_.isFile).toList.filter { file =>
        extensions.exists(file.getName.endsWith(_))
    }
}

lazy val root = (project in file("."))
  .settings(
    name := "inference-tool",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "net.liftweb" %% "lift-json" % "3.3.0",
    libraryDependencies += "commons-io" % "commons-io" % "2.6",
    libraryDependencies += "com.github.scopt" % "scopt_2.12" % "4.0.0-RC2",
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2",
    libraryDependencies += "log4j" % "log4j" % "1.2.16",
    libraryDependencies += "nz.ac.waikato.cms.weka" % "weka-dev" % "3.7.13",
    libraryDependencies += "org.apache.commons" % "commons-math3" % "3.6.1",
    libraryDependencies += "org.apache.commons" % "commons-collections4" % "4.1",
    libraryDependencies += "commons-cli" % "commons-cli" % "1.2",
    libraryDependencies += "com.googlecode.json-simple" % "json-simple" % "1.1",
    libraryDependencies += "org.biojava" % "biojava-structure" % "5.3.0",
    libraryDependencies += "org.jgrapht" % "jgrapht-core" % "1.1.0",
    libraryDependencies += "org.hammerlab.math" % "tolerance_2.11" % "1.0.1",

    cleanDotfiles := {
      cleanDirectory("dotfiles")
    },
    clean := clean.dependsOn(cleanDotfiles).value,
    mkdirs := {
      mkdir("dotfiles")
    },
    (run in Compile) := (run in Compile).dependsOn(mkdirs).evaluated,
    buildDOT := {
      for (f <- getListOfFiles(new File("dotfiles"), List("dot"))) {
        val b = f.getName().replaceFirst("[.][^.]+$", "");
        s"dot -T pdf -o dotfiles/${b}.pdf dotfiles/${b}.dot".!
      }
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
