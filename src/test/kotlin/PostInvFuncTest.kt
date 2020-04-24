import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class PostInvFuncTest : StringSpec({
	val postInv = PostInvType::class
	for (smt in listOf("z3", "cvc")) {
		println("testing with: $smt as backend")
		smtPath = smt
		"$smt basic1"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/functionsbasic.abs")))
			var funcDecl = model.extractFunctionDecl("M", "mult", repos)
			var mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true
			funcDecl = model.extractFunctionDecl("M", "multFail", repos)
			mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe false
		}
	}
})