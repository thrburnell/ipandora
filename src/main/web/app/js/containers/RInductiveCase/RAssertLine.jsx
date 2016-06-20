import { reduxForm, getValues } from 'redux-form'
import AssertLine from '../../components/InductiveCase/AssertLine'
import { closeInductiveCaseProofStep, makeAssertion } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeInductiveCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {

    console.log("Not yet implemented")
    reject()

    // if (!values.formula) {
    //   reject({ formula: "Undefined" })
    // } else if (!values.justification) {
    //   reject ({ justification: "Undefined" })
    // } else {
    //   dispatch(makeAssertion(values.formula, values.justification, "INDUCTIVE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ formula: "Invalid step", justification: "Invalid step" }))
    // }
  })
}

export default reduxForm({
  form: "addInductiveCaseProofLine",
  fields: ["formula", "justification"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssertLine)

