import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.smtPath
import org.abs_models.crowbar.types.RegAccType

class RegAccTest : StringSpec ({

	val regAcc = RegAccType::class
	val cvc: String = System.getenv("CVC") ?: "cvc"
	val z3: String = System.getenv("Z3") ?: "z3"
	for (smt in listOf(z3, cvc)) {
		println("testing with: $smt as backend")
		smtPath = smt
/*
		"$smt simple"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/simpleregacc.abs")))
			val classDecl = model.extractClassDecl("RegAcc", "C", repos)

			val s1Node = classDecl.extractMethodNode(regAcc,"m1", repos)
			shouldThrow<Exception> { executeNode(s1Node, repos, regAcc) }
			s1Node.collectInferenceLeaves().size shouldBe 1
			s1Node.collectInferenceLeaves().map { it.debugString(0) }.shouldBe(listOf("RA_A0 = acc: []"))

			val s2Node = classDecl.extractMethodNode(regAcc,"m2", repos)
			shouldThrow<Exception> { executeNode(s2Node, repos, regAcc)}
			s2Node.collectInferenceLeaves().size shouldBe 4
			s2Node.collectInferenceLeaves().map { it.debugString(0) }.shouldBe(
				listOf("RA_A1 = acc: [Rthis.f : Int, Rthis.g : Int, Wthis.g : Int] . RA_A2", "RA_A2 = acc: [Wthis.g : Int] . RA_A3", "RA_A3 = acc: [Rthis.f : Int] . RA_A4", "RA_A4 = acc: []"))

			val s3Node = classDecl.extractMethodNode(regAcc,"m3", repos)
			shouldThrow<Exception> { executeNode(s3Node, repos, regAcc)}
			s3Node.collectInferenceLeaves().size shouldBe 3
			s3Node.collectInferenceLeaves().map { it.debugString(0) }.shouldBe(
				listOf("RA_A5 = acc: [Wthis.g : Int] . RA_A6", "RA_A6 = acc: [Rthis.g : Int, Wthis.f : Int] . RA_A7", "RA_A7 = acc: []"))
			FreshGenerator.reset()
		}*/
	}
})