package scalafix.tests.cli

import java.io.ByteArrayOutputStream
import java.io.PrintStream
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import scala.collection.immutable.Seq
import scala.meta.internal.io.FileIO
import scalafix.cli.Cli
import scalafix.cli.CliCommand
import scalafix.cli.ExitStatus
import scalafix.internal.cli.CommonOptions
import scalafix.internal.cli.ScalafixOptions
import scalafix.internal.rule.RemoveUnusedImports
import scalafix.internal.tests.utils.SkipWindows
import scalafix.test.StringFS
import scalafix.testkit.DiffAssertions
import scalafix.testkit.SemanticRuleSuite
import scalafix.tests.BuildInfo
import ammonite.ops
import org.langmeta.io.AbsolutePath
import org.langmeta.io.RelativePath
import org.scalatest.FunSuite

// extend this class to run custom cli tests.
trait BaseCliTest extends FunSuite with DiffAssertions {
  val original: String =
    """|object Main {
       |  def foo() {
       |  }
       |}
       |""".stripMargin
  val expected: String =
    """|object Main {
       |  def foo(): Unit = {
       |  }
       |}
       |""".stripMargin
  val cwd: Path = Files.createTempDirectory("scalafix-cli")
  val ps = new PrintStream(new ByteArrayOutputStream())
  val devNull = CommonOptions(
    out = ps,
    err = ps,
    workingDirectory = cwd.toString
  )

  val default = ScalafixOptions(common = devNull)

  def check(
      name: String,
      originalLayout: String,
      args: Seq[String],
      expectedLayout: String,
      expectedExit: ExitStatus,
      outputAssert: String => Unit = _ => ()
  ): Unit = {
    test(name) {
      val out = new ByteArrayOutputStream()
      val root = StringFS.string2dir(originalLayout)
      val exit =
        Cli.runMain(
          args,
          default.common.copy(
            workingDirectory = root.toString(),
            out = new PrintStream(out)
          ))
      val obtained = StringFS.dir2string(root)
      assert(exit == expectedExit)
      assertNoDiff(obtained, expectedLayout)
      outputAssert(out.toString)
    }
  }

  def checkSuppress(
      name: String,
      originalFile: String,
      rule: String,
      expectedFile: String): Unit = {
    check(
      name,
      "/a.scala\n" + originalFile,
      Seq(
        "--auto-suppress-linter-errors",
        "-r",
        rule,
        "a.scala"
      ),
      "/a.scala\n" + expectedFile,
      ExitStatus.Ok
    )
    check(
      "check " + name,
      "/a.scala\n" + expectedFile,
      Seq(
        "--test",
        "-r",
        rule,
        "a.scala"
      ),
      "/a.scala\n" + expectedFile,
      ExitStatus.Ok
    )
  }

  val semanticRoot: RelativePath = RelativePath("scala").resolve("test")
  val removeImportsPath: RelativePath =
    semanticRoot.resolve("RemoveUnusedImports.scala")
  val explicitResultTypesPath: RelativePath =
    semanticRoot
      .resolve("explicitResultTypes")
      .resolve("ExplicitResultTypesBase.scala")
  val semanticClasspath =
    BuildInfo.semanticClasspath.getAbsolutePath

  def writeTestkitConfiguration(root: Path, path: Path): Unit = {
    import scala.meta._
    val code = new String(Files.readAllBytes(path), StandardCharsets.UTF_8)
    val comment = SemanticRuleSuite.findTestkitComment(code.tokenize.get)
    Files.write(
      root.resolve(".scalafix.conf"),
      comment.syntax.stripPrefix("/*").stripSuffix("*/").getBytes()
    )
  }
  def checkSemantic(
      name: String,
      args: Seq[String],
      expectedExit: ExitStatus,
      outputAssert: String => Unit = _ => (),
      rule: String = RemoveUnusedImports.toString(),
      path: RelativePath = removeImportsPath
  ): Unit = {
    test(name, SkipWindows) {
      val fileIsFixed = expectedExit.isOk
      val tmp = Files.createTempDirectory("scalafix")
      val out = new ByteArrayOutputStream()
      tmp.toFile.deleteOnExit()
      val root = ops.Path(tmp) / "input"
      ops.cp(ops.Path(BuildInfo.inputSourceroot.toPath), root)
      val rootNIO = root.toNIO
      writeTestkitConfiguration(rootNIO, rootNIO.resolve(path.toNIO))
      val exit = Cli.runMain(
        args ++ Seq(
          "-r",
          rule,
          path.toString()
        ),
        default.common.copy(
          workingDirectory = root.toString(),
          out = new PrintStream(out),
          err = new PrintStream(out)
        )
      )
      val obtained = {
        val fixed =
          FileIO.slurp(
            AbsolutePath(root.toNIO).resolve(path),
            StandardCharsets.UTF_8)
        if (fileIsFixed) SemanticRuleSuite.stripTestkitComments(fixed)
        else fixed
      }
      val expected =
        FileIO.slurp(
          AbsolutePath(
            if (fileIsFixed) BuildInfo.outputSourceroot
            else BuildInfo.inputSourceroot
          ).resolve(path),
          StandardCharsets.UTF_8
        )
      assert(exit == expectedExit)
      outputAssert(out.toString())
      if (expectedExit.isOk) {
        assertNoDiff(obtained, expected)
      }
    }
  }

  def parse(args: Seq[String]): CliCommand =
    Cli.parse(args, CommonOptions.default)
}
