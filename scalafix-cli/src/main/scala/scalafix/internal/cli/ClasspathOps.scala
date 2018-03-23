package scalafix.internal.cli

import java.io.File
import java.io.PrintStream
import scala.meta.Classpath
import scala.meta.metacp

object ClasspathOps {
  def toMclasspath(sclasspath: Classpath, out: PrintStream): Classpath = {
    val settings = metacp
      .Settings()
      .withClasspath(sclasspath)
      .withScalaLibrarySynthetics(true)
    val reporter = metacp.Reporter().withOut(out)
    val mclasspath = scala.meta.cli.Metacp.process(settings, reporter).get
    mclasspath
  }
  def getCurrentClasspath: String = {
    Thread.currentThread.getContextClassLoader match {
      case url: java.net.URLClassLoader =>
        url.getURLs.map(_.getFile).mkString(File.pathSeparator)
      case _ => ""
    }
  }
}
