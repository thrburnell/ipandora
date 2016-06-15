import { reduxForm, reset } from 'redux-form'
import { addGiven } from '../../actions'
import AddGiven from '../../components/Given/AddGiven'

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    dispatch(addGiven(values.formula))
      .then(() => dispatch(reset("addGiven")))
      .catch(() => reject({ formula: "Invalid syntax" }))
  })
}

export default reduxForm({
  form: "addGiven",
  fields: ["formula"],
  onSubmit: submit
})(AddGiven)

