import { reduxForm, getValues } from 'redux-form'
import AssertLine from '../../components/BaseCase/AssertLine'
import { closeBaseCaseProofStep, makeAssertion } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeBaseCaseProofStep())
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
    //   dispatch(makeAssertion(values.formula, values.justification, "BASE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ formula: "Invalid step", justification: "Invalid step" }))
    // }
  })
}

export default reduxForm({
  form: "addBaseCaseProofLine",
  fields: ["formula", "justification"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssertLine)

