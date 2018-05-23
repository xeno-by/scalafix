package scalafix.reflect

import metaconfig.Conf
import metaconfig.ConfDecoder
import metaconfig.ConfError
import metaconfig.Configured
import scalafix.Rule
import scalafix.SemanticdbIndex
import scalafix.internal.config._
import scalafix.internal.reflect.ScalafixCompilerDecoder
import scalafix.internal.util.ClassloadRule
import scalafix.internal.v1.LegacySemanticRule
import scalafix.internal.v1.LegacySyntacticRule
import scalafix.internal.v1.Rules
import scalafix.v1

object ScalafixReflect {
  def syntactic: ConfDecoder[Rule] =
    fromLazySemanticdbIndex(LazySemanticdbIndex.empty)

  def semantic(index: SemanticdbIndex): ConfDecoder[Rule] =
    fromLazySemanticdbIndex(LazySemanticdbIndex(_ => Some(index)))

  def fromLazySemanticdbIndex(index: LazySemanticdbIndex): ConfDecoder[Rule] =
    ruleConfDecoder(
      ScalafixCompilerDecoder
        .baseCompilerDecoder(index)
        .orElse(baseRuleDecoders(index))
    )
}
object ScalafixReflectV1 {

  def readSingleRule(
      rule: String,
      classloader: ClassLoader): Configured[v1.Rule] =
    // TODO: handle github: class: file:
    Rules.defaults.find(_.name.matches(rule)) match {
      case Some(r) => Configured.ok(r)
      case _ =>
        Conf.Str(rule) match {
          case UriRuleString("scala" | "class", fqn) =>
            tryClassload(classloader, fqn) match {
              case Some(r) =>
                Configured.ok(r)
              case _ =>
                ConfError.message(s"Class not found: $fqn").notOk
            }
          case UriRuleString("replace", replace @ SlashSeparated(from, to)) =>
//            requireSemanticSemanticdbIndex(index, replace) { m =>
//              parseReplaceSymbol(from, to)
//                .map(TreePatch.ReplaceSymbol.tupled)
//                .map(p => Rule.constant(replace, p, m))
//            }
            ???
        }
    }

  private lazy val legacySemanticRuleClass = classOf[scalafix.rule.SemanticRule]
  private lazy val legacyRuleClass = classOf[scalafix.rule.Rule]
  def toRule(cls: Class[_]): v1.Rule = {
    if (legacySemanticRuleClass.isAssignableFrom(cls)) {
      val fn: SemanticdbIndex => Rule = { index =>
        val ctor = cls.getDeclaredConstructor(classOf[SemanticdbIndex])
        ctor.setAccessible(true)
        ctor.newInstance(SemanticdbIndex.empty).asInstanceOf[scalafix.Rule]
      }
      new LegacySemanticRule(fn(SemanticdbIndex.empty).name, fn)
    } else if (legacyRuleClass.isAssignableFrom(cls)) {
      val ctor = cls.getDeclaredConstructor()
      ctor.setAccessible(true)
      new LegacySyntacticRule(ctor.newInstance().asInstanceOf[Rule])
    } else {
      val ctor = cls.getDeclaredConstructor()
      ctor.setAccessible(true)
      cls.newInstance().asInstanceOf[v1.Rule]
    }
  }

  def tryClassload(classloader: ClassLoader, fqn: String): Option[v1.Rule] = {
    try {
      Some(toRule(classloader.loadClass(fqn)))
    } catch {
      case _: ClassNotFoundException | _: NoSuchMethodException =>
        try {
          Some(toRule(classloader.loadClass(fqn + "$")))
        } catch {
          case _: ClassNotFoundException =>
            None
        }
    }
  }

  def decoder(): ConfDecoder[Rules] =
    decoder(ScalafixReporter.default, ClassloadRule.defaultClassloader)

  def decoder(
      reporter: ScalafixReporter,
      classloader: ClassLoader): ConfDecoder[Rules] =
    new ConfDecoder[Rules] {
      override def read(conf: Conf): Configured[Rules] = conf match {
        case str: Conf.Str =>
          read(Conf.Lst(str :: Nil))
        case Conf.Lst(values) =>
          val decoded = values.map {
            case Conf.Str(value) =>
              readSingleRule(value, classloader).map { r =>
                r.name.reportDeprecationWarning(value, reporter)
                r
              }
            case err =>
              ConfError.typeMismatch("String", err).notOk
          }
          MetaconfigPendingUpstream.flipSeq(decoded).map { rules =>
            Rules(rules.toList)
          }
        case els =>
          ConfError.typeMismatch("Either[String, List[String]]", els).notOk
      }
    }

}
